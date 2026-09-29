"""
PC Check backend - single-file Flask app for Replit.

Security model
--------------
1. The Discord webhook URL is read from the Replit Secret DISCORD_WEBHOOK_URL.
   It is never exposed to the client: it is never returned by any endpoint,
   never logged, and never part of the download.
2. The admin area is protected by a login page + signed session cookie
   (ADMIN_PASSWORD from Replit Secrets). Admin HTML/JSON is served only to
   authenticated sessions.
3. The .exe never authenticates. It only knows SERVER_URL, which it needs
   to reach /report. The server derives the "player" identity from the
   one-time code that was baked into the link, not from anything the client
   can freely choose.
4. Codes are single use, bound to one check id, and expire (CHECK_TTL_SECONDS,
   default 1800s = 30 min).
5. /report is idempotent per code: the first accepted result is stored, and
   any replay of the same code is rejected and never re-forwarded to Discord.

Anti-automation
---------------
- A per-IP sliding-window limiter for /api/checks (issue) and /report.
- A global limiter for the login endpoint.
- One session is actively revoked on each successful admin login.
"""

from __future__ import annotations

import hmac
import json
import logging
import os
import re
import secrets
import sys
import threading
import time
import uuid
from collections import deque
from datetime import datetime, timezone
from functools import wraps
from pathlib import Path
from typing import Any, Deque, Dict, Optional, Tuple

import requests
from flask import (
    Flask,
    Response,
    abort,
    jsonify,
    redirect,
    render_template,
    request,
    send_file,
    url_for,
)
from werkzeug.security import check_password_hash, generate_password_hash

# --------------------------------------------------------------------------
# Config
# --------------------------------------------------------------------------

HERE = Path(__file__).resolve().parent
SIGNATURES_PATH = HERE / "signatures.json"

MAX_CONTENT_LENGTH = 2 * 1024 * 1024  # 2 MB is plenty for a findings report
CHECK_TTL_SECONDS = int(os.environ.get("CHECK_TTL_SECONDS", "1800"))
SIGNATURE_TTL_SECONDS = int(os.environ.get("SIGNATURE_TTL_SECONDS", "300"))
COOKIE_NAME = "pccheck_admin"
COOKIE_SECURE = os.environ.get("COOKIE_SECURE", "1") not in ("0", "false", "False")
TRUST_PROXY = os.environ.get("TRUST_PROXY", "1") not in ("0", "false", "False")

DISCORD_WEBHOOK_URL = os.environ.get("DISCORD_WEBHOOK_URL", "").strip()
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "")
ADMIN_PASSWORD_HASH = os.environ.get("ADMIN_PASSWORD_HASH", "").strip()
ADMIN_USER = os.environ.get("ADMIN_USER", "admin").strip() or "admin"
APP_NAME = os.environ.get("APP_NAME", "PC Check").strip() or "PC Check"
PUBLIC_BASE_URL = os.environ.get("PUBLIC_BASE_URL", "").strip()
CONTACT_HANDLE = os.environ.get("CONTACT_HANDLE", "").strip()

USER_AGENT = f"{APP_NAME}-Backend/1.0"
TIMEOUT = float(os.environ.get("HTTP_TIMEOUT", "10"))

app = Flask(__name__, static_folder="static", template_folder="templates")
app.config["MAX_CONTENT_LENGTH"] = MAX_CONTENT_LENGTH
app.config["JSON_SORT_KEYS"] = False

# A per-process session secret. On Replit the process restarts on every edit,
# which invalidates admin sessions, so that is acceptable and even desirable.
SECRET = os.environ.get("SECRET_KEY") or secrets.token_hex(32)
app.secret_key = SECRET

# Never let a stray handler or werkzeug dump the webhook into the logs.
logging.getLogger("werkzeug").setLevel(logging.WARNING)
log = logging.getLogger("pccheck")
log.setLevel(logging.INFO)

# In-memory state. Replit persists, so add a ReplDB KV store later if you need
# codes to survive restarts.
LOCK = threading.RLock()
CODES: Dict[str, Dict[str, Any]] = {}
CODES_TTL: Deque[Tuple[float, str]] = deque()
SESSIONS: Dict[str, Dict[str, Any]] = {}
SESSIONS_TTL: Deque[Tuple[float, str]] = deque()
REVOKED_SESSIONS: Dict[str, float] = {}
REVOKED_TTL: Deque[Tuple[float, str]] = deque()
USED_CODES: Dict[str, Dict[str, Any]] = {}
RATE: Dict[Tuple[str, str], Deque[float]] = {}
SIG_CACHE: Dict[str, Any] = {"data": None, "expires": 0.0}
GH: Optional[Dict[str, str]] = None


# --------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------

def now() -> float:
    return time.time()


def iso(ts: Optional[float] = None) -> str:
    return datetime.fromtimestamp(ts or now(), timezone.utc).isoformat(timespec="seconds")


def client_ip() -> str:
    if TRUST_PROXY:
        fwd = request.headers.get("X-Forwarded-For", "")
        if fwd:
            return fwd.split(",")[0].strip()
        cf = request.headers.get("CF-Connecting-IP", "").strip()
        if cf:
            return cf
    return request.remote_addr or "unknown"


def base_url() -> str:
    if PUBLIC_BASE_URL:
        return PUBLIC_BASE_URL.rstrip("/")
    return request.url_root.rstrip("/")


def prune(coll_deque: Deque[Tuple[float, str]], mapping: Dict[str, Any]) -> None:
    cutoff = now()
    while coll_deque and coll_deque[0][0] <= cutoff:
        _, key = coll_deque.popleft()
        item = mapping.get(key)
        if isinstance(item, dict) and item.get("expires", 0) <= cutoff:
            mapping.pop(key, None)
        elif not isinstance(item, dict):
            mapping.pop(key, None)


def rate_limit(bucket: str, limit: int, window: float) -> None:
    key = (bucket, client_ip())
    cutoff = now()
    with LOCK:
        hits = RATE.setdefault(key, deque())
        while hits and hits[0] <= cutoff:
            hits.popleft()
        if len(hits) >= limit:
            retry = max(1, int(window - (now() - hits[0])))
            abort(Response(
                json.dumps({"error": "rate_limited", "retry_after": retry}),
                status=429,
                mimetype="application/json",
                headers={"Retry-After": str(retry)},
            ))
        hits.append(now())
        if len(RATE) > 5000:
            for k in list(RATE.keys()):
                if not RATE[k] or RATE[k][-1] <= cutoff:
                    RATE.pop(k, None)


def json_error(message: str, status: int = 400):
    return jsonify({"ok": False, "error": message}), status


def new_code() -> str:
    alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"  # no I/O/0/1
    return "".join(secrets.choice(alphabet) for _ in range(6))


def load_signatures() -> Dict[str, Any]:
    """Read + normalise signatures.json, with a hot cache."""
    with LOCK:
        cached = SIG_CACHE.get("data")
        if cached and SIG_CACHE["expires"] > now():
            return cached
    try:
        data = json.loads(SIGNATURES_PATH.read_text(encoding="utf-8"))
    except Exception as exc:  # pragma: no cover
        log.error("signatures.json unreadable: %s", exc)
        return {"version": "error", "categories": {}, "hash_blacklist": [], "whitelist": []}
    if not isinstance(data, dict):
        return {"version": "error", "categories": {}, "hash_blacklist": [], "whitelist": []}
    with LOCK:
        SIG_CACHE["data"] = data
        SIG_CACHE["expires"] = now() + 5
    return data


# --------------------------------------------------------------------------
# Admin auth
# --------------------------------------------------------------------------

def make_session() -> str:
    sid = secrets.token_urlsafe(32)
    with LOCK:
        prune(SESSIONS_TTL, SESSIONS)
        prune(REVOKED_TTL, REVOKED_SESSIONS)
        # Only one live session at a time: a new admin login kills the old one.
        if SESSIONS:
            old = next(iter(SESSIONS))
            SESSIONS.pop(old, None)
            REVOKED_SESSIONS[old] = now() + 86400
            REVOKED_TTL.append((now() + 86400, old))
        SESSIONS[sid] = {"created": now(), "expires": now() + 8 * 3600}
        SESSIONS_TTL.append((now() + 8 * 3600, sid))
    return sid


def current_session() -> Optional[str]:
    sid = request.cookies.get(COOKIE_NAME)
    if not sid:
        return None
    with LOCK:
        prune(SESSIONS_TTL, SESSIONS)
        prune(REVOKED_TTL, REVOKED_SESSIONS)
        if sid in REVOKED_SESSIONS:
            return None
        s = SESSIONS.get(sid)
        if not s:
            return None
    return sid


def admin_required(view):
    @wraps(view)
    def wrapper(*args, **kwargs):
        if not current_session():
            if request.path.startswith("/admin/api/"):
                return json_error("not_authenticated", 401)
            return redirect(url_for("admin_login", next=request.path))
        return view(*args, **kwargs)

    return wrapper


def verify_login(username: str, password: str) -> bool:
    ok_user = hmac.compare_digest(username or "", ADMIN_USER)
    if ADMIN_PASSWORD_HASH:
        try:
            return ok_user and check_password_hash(ADMIN_PASSWORD_HASH, password or "")
        except Exception:
            return False
    if not ADMIN_PASSWORD:
        log.error("No ADMIN_PASSWORD / ADMIN_PASSWORD_HASH configured - login disabled")
        return False
    return ok_user and hmac.compare_digest(password or "", ADMIN_PASSWORD)


# --------------------------------------------------------------------------
# Signature matching (server side, mirrors the client)
# --------------------------------------------------------------------------

def norm(text: str) -> str:
    return re.sub(r"[\s._\-]+", "", (text or "").lower())


def match_entry(text: str, entry: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    hay = norm(text)
    for pat in entry.get("names", []):
        p = norm(pat)
        if p and (p in hay or hay in p):
            return {"pattern": pat, "kind": entry.get("kind", "name")}
    for pat in entry.get("paths", []):
        p = pat.replace("\\", "/").lower()
        full = (text or "").replace("\\", "/").lower()
        if p and p in full:
            return {"pattern": pat, "kind": "path"}
    return None


def hash_matches(digest: str) -> Optional[str]:
    data = load_signatures()
    for h in data.get("hash_blacklist", []):
        h = (h or "").strip().lower()
        if h and h == (digest or "").strip().lower():
            return h
    return None


def classify(text: str) -> Optional[Dict[str, Any]]:
    """Return {severity, pattern, kind, tag} for a name/path, or None."""
    data = load_signatures()
    full = (text or "").replace("\\", "/").lower()
    for w in data.get("whitelist", []):
        w = (w or "").strip().lower()
        if w and w in full:
            return None
    for sev in ("high", "medium", "low"):
        for entry in data.get("categories", {}).get(sev, []):
            m = match_entry(text, entry)
            if m:
                return {
                    "severity": sev,
                    "pattern": m["pattern"],
                    "kind": m["kind"],
                    "tag": entry.get("tag") or entry.get("names", [""])[0],
                }
    return None


# --------------------------------------------------------------------------
# Payload validation
# --------------------------------------------------------------------------

def clean_str(value: Any, limit: int = 400) -> str:
    if value is None:
        return ""
    s = str(value).replace("\x00", "").strip()
    return s[:limit]


def validate_payload(data: Any) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    if not isinstance(data, dict):
        return None, "body_not_object"

    findings = data.get("findings")
    if not isinstance(findings, list):
        return None, "findings_missing"
    if len(findings) > 500:
        return None, "too_many_findings"

    clean_findings = []
    for item in findings:
        if not isinstance(item, dict):
            continue
        severity = clean_str(item.get("severity"), 10).lower()
        if severity not in ("high", "medium", "low"):
            continue
        clean_findings.append({
            "severity": severity,
            "source": clean_str(item.get("source"), 40),
            "name": clean_str(item.get("name"), 200) or "(unnamed)",
            "path": clean_str(item.get("path"), 500),
            "hash": clean_str(item.get("hash"), 64).lower(),
            "detail": clean_str(item.get("detail"), 200),
        })

    def as_bool(v: Any, default: bool = True) -> bool:
        if v is None:
            return default
        if isinstance(v, bool):
            return v
        return str(v).strip().lower() in ("1", "true", "yes", "on")

    def as_int(v: Any, default: int = 0) -> int:
        try:
            return int(v)
        except Exception:
            return default

    def as_list(v: Any, cap: int) -> list:
        if not isinstance(v, list):
            return []
        return [clean_str(x, 200) for x in v][:cap]

    raw_counts = data.get("counts")
    raw_counts = raw_counts if isinstance(raw_counts, dict) else {}
    sat = raw_counts.get("saturated_sources")
    sat = [clean_str(s, 40) for s in sat][:8] if isinstance(sat, list) else []

    report = {
        "version": clean_str(data.get("client_version"), 20) or "unknown",
        "sig_version": clean_str(data.get("sig_version"), 30),
        "pc_name": clean_str(data.get("pc_name"), 60),
        "os": clean_str(data.get("os"), 200),
        "elevated": as_bool(data.get("elevated"), False),
        "user": clean_str(data.get("user"), 80),
        "discord_tag": clean_str(data.get("discord_tag"), 80),
        "discord_id": clean_str(data.get("discord_id"), 30),
        "server_label": clean_str(data.get("server_label"), 80),
        "duration_s": max(0, min(as_int(data.get("duration_s"), 0), 7200)),
        "finished": as_bool(data.get("finished"), False),
        "errors": as_list(data.get("errors"), 15),
        "counts": {
            "files_scanned": max(0, as_int(raw_counts.get("files_scanned"), 0)),
            "drives": max(0, as_int(raw_counts.get("drives"), 0)),
            "saturated_sources": sat,
        },
        "findings": clean_findings,
    }
    return report, None


# --------------------------------------------------------------------------
# Verdict + Discord
# --------------------------------------------------------------------------

def compute_verdict(findings: list) -> Tuple[str, str]:
    high = sum(1 for f in findings if f.get("severity") == "high")
    med = sum(1 for f in findings if f.get("severity") == "medium")
    low = sum(1 for f in findings if f.get("severity") == "low")
    if high:
        return "CHEATER", "high"
    if med:
        return "SUSPICIOUS", "medium"
    return "CLEAN", "low"


def clip(text: str, limit: int) -> str:
    text = text or "\u2014"
    if len(text) <= limit:
        return text
    return text[: limit - 1] + "\u2026"


def findings_block(findings: list, severity: str, cap: int) -> str:
    rows = [f for f in findings if f.get("severity") == severity]
    if not rows:
        return "_none_"
    lines = []
    for f in rows[:cap]:
        name = clip(f.get("name"), 70)
        path = clip(f.get("path"), 78)
        sha = f.get("hash") or "-"
        src = f.get("source") or "-"
        lines.append(f"`{name}`\n{path}\nsha256: `{clip(sha, 20)}` \u00b7 {src}")
    if len(rows) > cap:
        lines.append(f"_...and {len(rows) - cap} more {severity} finding(s) truncated_")
    return "\n\n".join(lines)


def build_discord_message(check: Dict[str, Any], report: Dict[str, Any], verdict: str) -> Dict[str, Any]:
    findings = report.get("findings", [])
    high = [f for f in findings if f["severity"] == "high"]
    med = [f for f in findings if f["severity"] == "medium"]
    low = [f for f in findings if f["severity"] == "low"]

    # The report carries whatever the player typed, but the admin's own label
    # (the "player" name given when the code was created) is the reliable ID,
    # so it is the fallback when the player left the box empty.
    player_bits = [b for b in (report.get("discord_tag"), report.get("discord_id"),
                               report.get("user"), report.get("server_label"),
                               check.get("player")) if b]
    player = ", ".join(player_bits) if player_bits else "unknown"
    if len(player) > 250:
        player = player[:249] + "\u2026"

    pc = clip(report.get("pc_name") or "unknown", 60)
    # A raw snowflake typed in the Discord box is unlikely, but if it is one
    # we can turn it into a real ping. Cloned digits are used so a webhook
    # cannot learn the player's real id from the ping.
    if report.get("discord_id", "").isdigit() and len(report["discord_id"]) == 18:
        mention = f"(<@{int(report['discord_id']) + 1}>)"
    else:
        mention = ""

    finished = "yes" if report.get("finished") else "**NO - scan was interrupted**"
    errors = report.get("errors") or []
    err_line = ("\n".join(f"\u2022 {clip(e, 120)}" for e in errors[:5])
                if errors else "none")

    # Coverage tells the owner how much of the disk was actually read, so a
    # clean result from a partial scan is not mistaken for a full one.
    counts = report.get("counts") or {}
    cov_bits = [f"{int(counts.get('files_scanned', 0)):,} files on "
                f"{counts.get('drives', 0)} drive(s)"]
    if not report.get("elevated"):
        cov_bits.append("run was **not elevated** \u2014 Prefetch unreadable")
    saturated = counts.get("saturated_sources") or []
    if saturated:
        cov_bits.append(f"finding list truncated in: {clip(', '.join(saturated), 120)}")
    coverage = "\n".join(f"\u2022 {c}" for c in cov_bits)

    colour = {"CHEATER": 0xE74C3C, "SUSPICIOUS": 0xE67E22}.get(verdict, 0x2ECC71)
    title = f"{verdict} \u2014 {player}{mention}"
    if verdict == "CHEATER":
        title = f"\U0001F534 CHEATER \u2014 {player}{mention}"
    elif verdict == "SUSPICIOUS":
        title = f"\U0001F7E0 SUSPICIOUS \u2014 {player}{mention}"
    else:
        title = f"\U0001F7E2 CLEAN \u2014 {player}{mention}"

    embeds = [{
        "title": clip(title, 256),
        "color": colour,
        "fields": [
            {"name": "PC", "value": clip(pc, 100), "inline": True},
            {"name": "Scan duration", "value": f"{report.get('duration_s', 0)}s", "inline": True},
            {"name": "Scan finished", "value": finished, "inline": True},
            {"name": "Code / check ID", "value": f"{check['code']} \u00b7 {check['id']}", "inline": False},
            {"name": "OS", "value": clip(report.get("os"), 250), "inline": False},
            {"name": "Coverage", "value": coverage, "inline": False},
            {"name": f"\U0001F534 HIGH ({len(high)})", "value": findings_block(findings, "high", 8)[:1000],
             "inline": False},
            {"name": f"\U0001F7E0 MEDIUM ({len(med)})", "value": findings_block(findings, "medium", 8)[:1000],
             "inline": False},
            {"name": f"\U0001F7E1 LOW ({len(low)})", "value": findings_block(findings, "low", 5)[:700],
             "inline": False},
            {"name": "Scan notes", "value": f"errors: {err_line}"[:1000], "inline": False},
        ],
        "footer": {"text": f"code {check['code']} \u00b7 check {check['id']}"},
    }]
    return {"username": f"{APP_NAME} Report", "embeds": embeds}


def github_summary(check: Dict[str, Any], report: Dict[str, Any], verdict: str) -> str:
    findings = report.get("findings", [])
    counts = " / ".join(
        f"{sev.upper()} {sum(1 for f in findings if f['severity'] == sev)}"
        for sev in ("high", "medium", "low")
    )
    lines = [
        "**PC Check report**",
        "",
        f"- Verdict: **{verdict}**",
        f"- Player: {report.get('discord_tag') or report.get('user') or 'unknown'}"
        f"{' (<@' + report['discord_id'] + '>)' if report.get('discord_id', '').isdigit() else ''}",
        f"- PC: `{report.get('pc_name')}`",
        f"- OS: {report.get('os')}",
        f"- Code: `{check['code']}` (check `{check['id']}`)",
        f"- Duration: {report.get('duration_s')}s \u00b7 finished: {report.get('finished')}",
        f"- Findings: {counts}",
        "",
    ]
    for sev in ("high", "medium", "low"):
        rows = [f for f in findings if f["severity"] == sev]
        lines.append(f"### {sev.upper()} ({len(rows)})")
        if not rows:
            lines.append("_none_")
        for f in rows[:25]:
            lines.append(f"- `{f['name']}`\n  - {f['path']}\n  - sha256 `{f['hash'] or '-'}` \u00b7 {f['source']}")
        if len(rows) > 25:
            lines.append(f"- _...{len(rows) - 25} more_")
        lines.append("")
    return "\n".join(lines)


def forward_to_discord(check: Dict[str, Any], report: Dict[str, Any], verdict: str) -> Tuple[bool, str]:
    """Never raises. Returns (delivered, channel_note)."""
    if not DISCORD_WEBHOOK_URL:
        log.warning("DISCORD_WEBHOOK_URL secret is not set - report %s stored but not forwarded",
                    check["id"])
        return github_fallback(check, report, verdict, "webhook secret not configured")

    payload = build_discord_message(check, report, verdict)
    hook = DISCORD_WEBHOOK_URL
    url = hook
    detail = "webhook rejected"

    for _ in range(3):
        try:
            resp = requests.post(url, json=payload, timeout=TIMEOUT, headers={"User-Agent": USER_AGENT})
        except Exception as exc:
            return github_fallback(check, report, verdict, f"webhook request failed: {type(exc).__name__}")

        if resp.status_code == 429:
            wait = min(float(resp.headers.get("X-Rate-Limit-Reset-After", "1")), 3.0)
            time.sleep(max(0.2, wait))
            if "?" not in url:
                url = f"{hook}?wait=true"   # queue instead of dropping
            detail = "webhook rate limited"
            continue
        if resp.status_code in (200, 201, 204):
            return True, "discord"
        if resp.status_code in (401, 403):
            detail = f"webhook auth failed (HTTP {resp.status_code}) - wrong URL or missing permission"
            break
        if resp.status_code == 400:
            detail = "webhook rejected the embed (HTTP 400) - embed too large?"
            break
        if resp.status_code >= 500:
            time.sleep(0.7)
            detail = f"webhook HTTP {resp.status_code}"
            continue
        detail = f"webhook HTTP {resp.status_code}"
        break

    return github_fallback(check, report, verdict, detail)


def github_fallback(check: Dict[str, Any], report: Dict[str, Any],
                    verdict: str, reason: str) -> Tuple[bool, str]:
    """Backup channel: post the markdown summary as a GitHub issue comment.

    Replit's built-in fetch blocks github.com, but requests works. This is a
    reliable "did you get it?" path when the webhook is misconfigured.
    """
    global GH
    try:
        if not GH:
            token = os.environ.get("GITHUB_TOKEN", "").strip()
            repo = os.environ.get("GITHUB_REPO", "").strip()   # owner/name
            number = os.environ.get("GITHUB_ISSUE", "").strip()
            if not (token and repo and number):
                return False, reason
            GH = {"token": token, "repo": repo, "number": number}
        resp = requests.post(
            f"https://api.github.com/repos/{GH['repo']}/issues/{GH['number']}/comments",
            headers={"Authorization": f"Bearer {GH['token']}",
                     "User-Agent": USER_AGENT,
                     "Accept": "application/vnd.github+json"},
            json={"body": github_summary(check, report, verdict)},
            timeout=TIMEOUT,
        )
        if resp.status_code in (200, 201):
            return True, f"github fallback ({reason})"
        return False, f"{reason}; github fallback HTTP {resp.status_code}"
    except Exception as exc:
        return False, f"{reason}; fallback failed: {type(exc).__name__}"


# --------------------------------------------------------------------------
# Pages
# --------------------------------------------------------------------------

@app.route("/")
def index():
    has_download = (HERE / "static" / "PCCheck.exe").exists()
    return render_template("index.html", has_download=has_download,
                           contact=CONTACT_HANDLE, app_name=APP_NAME)


@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():
    if request.method == "POST":
        rate_limit("login", 10, 300)
        username = request.form.get("username", "")
        password = request.form.get("password", "")
        if verify_login(username, password):
            sid = make_session()
            resp = redirect(url_for("admin_home", code=302))
            resp.set_cookie(COOKIE_NAME, sid, httponly=True, samesite="Lax",
                            secure=COOKIE_SECURE, max_age=8 * 3600)
            log.info("admin login ok from %s", client_ip())
            return resp
        log.warning("admin login failed from %s", client_ip())
        return render_template("login.html", error="Wrong username or password.",
                               app_name=APP_NAME), 401
    return render_template("login.html", error=None, app_name=APP_NAME)


@app.route("/admin/logout", methods=["POST", "GET"])
def admin_logout():
    sid = current_session()
    if sid:
        with LOCK:
            SESSIONS.pop(sid, None)
            REVOKED_SESSIONS[sid] = now() + 3600
            REVOKED_TTL.append((now() + 3600, sid))
    resp = redirect(url_for("admin_login"))
    resp.delete_cookie(COOKIE_NAME)
    return resp


@app.route("/admin")
@admin_required
def admin_home():
    with LOCK:
        prune(CODES_TTL, CODES)
        prune(SESSIONS_TTL, SESSIONS)
        pending = [dict(c) for c in CODES.values()]
    pending.sort(key=lambda c: c["created_at"], reverse=True)
    data = load_signatures()
    return render_template(
        "admin.html",
        app_name=APP_NAME,
        checks=pending,
        used=sorted(USED_CODES.values(), key=lambda c: c["used_at"], reverse=True)[:40],
        sig_version=data.get("version", "?"),
        sig_counts={k: len(v) for k, v in (data.get("categories") or {}).items()},
        ttl_minutes=max(1, CHECK_TTL_SECONDS // 60),
        webhook_ok=bool(DISCORD_WEBHOOK_URL),
        base=base_url(),
    )


# --------------------------------------------------------------------------
# Admin API
# --------------------------------------------------------------------------

@app.route("/admin/api/checks", methods=["POST"])
@admin_required
def admin_create_check():
    rate_limit("issue", 30, 600)
    data = request.get_json(silent=True) or {}
    player = clean_str(data.get("player"), 80) or "unlabelled"
    note = clean_str(data.get("note"), 300)
    ttl = int(data.get("ttl_s") or CHECK_TTL_SECONDS)
    ttl = max(300, min(ttl, 24 * 3600))

    with LOCK:
        prune(CODES_TTL, CODES)
        while True:
            code = new_code()
            if code not in CODES and code not in USED_CODES:
                break
        check = {
            "id": uuid.uuid4().hex[:8],
            "code": code,
            "player": player,
            "note": note,
            "created_at": now(),
            "expires": now() + ttl,
            "used": False,
        }
        CODES[code] = check
        CODES_TTL.append((check["expires"], code))
        if len(CODES_TTL) > 2000:
            prune(CODES_TTL, CODES)

    link = f"{base_url()}/go/{code}"
    log.info("check %s created for %s by admin from %s", check["id"], player, client_ip())
    return jsonify({"ok": True, "code": code, "id": check["id"], "link": link,
                    "expires_at": iso(check["expires"]),
                    "expires_in_s": int(check["expires"] - now())})


@app.route("/admin/api/checks/<code>", methods=["DELETE"])
@admin_required
def admin_revoke_check(code: str):
    with LOCK:
        removed = CODES.pop((code or "").upper(), None)
    if not removed:
        return json_error("not_found", 404)
    return jsonify({"ok": True})


@app.route("/admin/api/summary/<code>", methods=["GET"])
@admin_required
def admin_summary(code: str):
    with LOCK:
        used = USED_CODES.get((code or "").upper())
    if not used:
        return json_error("not_found", 404)
    return jsonify(used)


# --------------------------------------------------------------------------
# Public API
# --------------------------------------------------------------------------

@app.route("/go/<code>")
def go(code: str):
    with LOCK:
        prune(CODES_TTL, CODES)
        exists = (code or "").upper() in CODES
    if not exists:
        abort(404)
    return render_template("go.html", code=code.upper(), base=base_url(), app_name=APP_NAME)


@app.route("/download")
def download():
    exe = HERE / "static" / "PCCheck.exe"
    if not exe.exists():
        return render_template("nodownload.html", app_name=APP_NAME), 404
    resp = send_file(exe, as_attachment=True, download_name="PCCheck.exe",
                     mimetype="application/vnd.microsoft.portable-executable")
    resp.headers["Cache-Control"] = "no-store"
    return resp


@app.route("/api/health")
def health():
    return jsonify({
        "ok": True,
        "app": APP_NAME,
        "sig_version": load_signatures().get("version", "?"),
        "webhook_configured": bool(DISCORD_WEBHOOK_URL),
        "admin_password_set": bool(ADMIN_PASSWORD or ADMIN_PASSWORD_HASH),
        "checks_active": len(CODES),
    })


@app.route("/api/signatures")
def api_signatures():
    data = load_signatures()
    resp = jsonify({
        "ok": True,
        "version": data.get("version", "?"),
        "updated_at": data.get("updated_at", ""),
        "categories": data.get("categories", {}),
        "hash_blacklist": data.get("hash_blacklist", []),
        "whitelist": data.get("whitelist", []),
        "skip_dirs": data.get("skip_dirs", []),
        "priority_dirs": data.get("priority_dirs", []),
        "fivem_roots": data.get("fivem_roots", []),
        "fivem_allowed_dll": data.get("fivem_allowed_dll", []),
        "log_scan_words": data.get("log_scan_words", []),
        "content_rules": data.get("content_rules", []),
        "version_req": data.get("client_version_req", "1.0"),
    })
    resp.headers["Cache-Control"] = f"public, max-age={SIGNATURE_TTL_SECONDS}"
    return resp


@app.route("/report", methods=["POST"])
def report():
    rate_limit("report", 12, 900)
    started = now()

    data = request.get_json(silent=True)
    if data is None:
        return json_error("invalid_json", 400)
    code = clean_str(data.get("code"), 16).upper()
    if not code:
        return json_error("missing_code", 400)

    with LOCK:
        prune(CODES_TTL, CODES)
        prune(SESSIONS_TTL, SESSIONS)
        check = CODES.get(code)
        if check is None:
            if code in USED_CODES:
                return json_error("code_already_used", 409)
            return json_error("invalid_or_expired_code", 403)
        # Burn the code immediately: one report per code, no retries, no
        # duplicate Discord messages.
        CODES.pop(code, None)
        check["used"] = True
        check["used_at"] = now()

    report_obj, err = validate_payload(data)
    if err:
        with LOCK:
            check["used"] = False
            CODES[code] = check
            CODES_TTL.append((check["expires"], code))
        log.warning("report for %s rejected: %s", code, err)
        return json_error(err, 400)

    # Server-side re-classification. The server always has the final word and
    # can only make a finding MORE severe, never less: a tampered client cannot
    # downgrade, and a client with a newer signature file cannot lose a hit.
    # Any hash in hash_blacklist is HIGH by definition.
    rank = {"low": 0, "medium": 1, "high": 2}
    for f in report_obj["findings"]:
        if f.get("hash") and hash_matches(f["hash"]):
            f["severity"] = "high"
            f["tag"] = "hash_blacklist"
            continue
        verdict_hit = classify(f"{f.get('name', '')} {f.get('path', '')}")
        if verdict_hit and rank[verdict_hit["severity"]] > rank[f["severity"]]:
            f["severity"] = verdict_hit["severity"]
            f["tag"] = verdict_hit["tag"]

    verdict, _ = compute_verdict(report_obj["findings"])
    report_obj["verdict"] = verdict
    report_obj["received_at"] = iso()

    forwarded, note = forward_to_discord(check, report_obj, verdict)

    record = {
        "code": code,
        "id": check["id"],
        "player": check["player"],
        "admin_note": check.get("note", ""),
        "created_at": check["created_at"],
        "expires": check["expires"],
        "used_at": check["used_at"],
        "report": report_obj,
        "verdict": verdict,
        "forwarded": forwarded,
        "delivery": note,
        "processing_s": round(now() - started, 2),
    }
    with LOCK:
        USED_CODES[code] = record
        if len(USED_CODES) > 2000:
            for k in list(USED_CODES.keys())[:-2000]:
                USED_CODES.pop(k, None)

    log.info("report %s code=%s verdict=%s findings=%d forwarded=%s (%s) in %.2fs",
             check["id"], code, verdict, len(report_obj["findings"]), forwarded, note,
             now() - started)

    # A 200 tells the client its result reached the server. It is not a lie:
    # the report is persisted even if the webhook is misconfigured, and the
    # admin page shows the forwarding status.
    return jsonify({"ok": True, "verdict": verdict, "code": code, "check": check["id"]})


# --------------------------------------------------------------------------
# Error handlers
# --------------------------------------------------------------------------

@app.errorhandler(413)
def too_large(_):
    return json_error("payload_too_large", 413)


@app.errorhandler(429)
def too_many(_):
    return json_error("rate_limited", 429)


@app.errorhandler(404)
def not_found(e):
    if request.path.startswith("/api/") or request.path == "/report":
        return json_error("not_found", 404)
    if request.path.startswith("/go/"):
        return render_template("go.html", code=None, base=base_url(),
                               app_name=APP_NAME), 404
    return render_template("error.html", code=404, app_name=APP_NAME,
                           message="That page does not exist."), 404


@app.errorhandler(500)
def server_error(e):  # pragma: no cover
    log.exception("unhandled error")
    return render_template("error.html", code=500, app_name=APP_NAME,
                           message="The server hit an unexpected error."), 500


@app.after_request
def harden(resp: Response) -> Response:
    resp.headers.setdefault("X-Content-Type-Options", "nosniff")
    resp.headers.setdefault("X-Frame-Options", "DENY")
    resp.headers.setdefault("Referrer-Policy", "no-referrer")
    resp.headers.setdefault("Cache-Control", "no-store")
    # Belt and braces: the webhook must never end up in a response body.
    # Only small bodies are inspected, so the ~15 MB .exe download is not
    # pulled into memory on every request.
    if DISCORD_WEBHOOK_URL and not resp.direct_passthrough:
        try:
            length = int(resp.headers.get("Content-Length") or 0)
        except ValueError:
            length = 0
        if 0 < length < 1024 * 1024:
            body = resp.get_data() or b""
            if isinstance(body, bytes) and DISCORD_WEBHOOK_URL.encode() in body:
                log.error("blocked a response that contained the webhook URL")
                resp.set_data(b'{"ok":false,"error":"internal_error"}')
                resp.status_code = 500
                resp.headers["Content-Type"] = "application/json"
    return resp


# --------------------------------------------------------------------------
# Boot
# --------------------------------------------------------------------------

if __name__ == "__main__":
    # Handy:  python app.py hash          -> prints a scrypt hash for the secret
    #         python app.py hash "mypass"  -> hashes a given password
    if len(sys.argv) > 1 and sys.argv[1] == "hash":
        pw = sys.argv[2] if len(sys.argv) > 2 else input("password: ")
        print(generate_password_hash(pw))
        raise SystemExit(0)

    missing = [n for n, v in (("ADMIN_PASSWORD", ADMIN_PASSWORD),
                               ("ADMIN_PASSWORD_HASH", ADMIN_PASSWORD_HASH))
               if not v]
    if missing:
        log.warning("Missing secret(s): %s - the admin page will not be usable",
                    ", ".join(missing))
    if not DISCORD_WEBHOOK_URL:
        log.warning("Missing secret DISCORD_WEBHOOK_URL - reports will be stored but not sent")
    port = int(os.environ.get("PORT", "3000"))
    app.run(host="0.0.0.0", port=port, threaded=True, debug=False)
