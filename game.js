/**
 * 19×19 오목: 사용자 vs 컴퓨터, 정확히 5연속만 승.
 * 돌은 격자 교차점에 둠. 사용자 차례에 20초 내 미착수 시 상대(컴퓨터) 차례로 넘김.
 * 승리 후 대화상자에서 다음 판 흑·백 선택 가능.
 * 컴퓨터 착수: 즉승·즉패 후 이중위협 조건부 막기, 미니맥스 깊이·후보폭 단계별 상향. 탐색 중 주기적으로 setTimeout으로 양보해 AI 20초 타이머가 막히지 않게 함. 제한 시간이 지나면 착수 없이 사용자 차례로 넘김.
 * 후보가 많을 때 변·쪽 막수·상대 이중 위협 막수를 넣되, 정적 평가는 공격 비중을 높게 잡음.
 * 빈 판 첫 수는 천원에 즉시 두고, 돌 1~2개 구간은 미니맥스 없이 탐욕 후보만 써서 초반 대기 시간을 줄임.
 */
(function () {
  const SIZE = 19;
  const EMPTY = 0;
  const BLACK = 1;
  const WHITE = 2;
  const MOVE_LIMIT_SEC = 20;
  /** 미니맥스가 실제 연산 시간을 쓰므로, 긴 인위 대기는 두지 않음. 화면 갱신 후 착수까지 짧은 지터만 */
  const AI_THINK_JITTER_MIN_MS = 30;
  const AI_THINK_JITTER_MAX_MS = 70;
  /** 미니맥스 최대 깊이 — 초반에는 effectiveSearchDepthPlies()로 완만히 제한 */
  const AI_SEARCH_PLIES = 5;
  /** 한 노드 후보 상한 — 알파-베타·정렬 후 실제 노드 수는 통상 이보다 적음 */
  const AI_MAX_BRANCH = 24;
  const AI_EVAL_WIN = 1e12;
  /** 미니맥스 노드마다 양보하면 과도하게 느려지므로 N회마다 setTimeout(0)으로 매크로태스크 양보 — 마이크로태스크만 쌓이면 AI 타이머 인터벌이 실행되지 않음 */
  const MINIMAX_YIELD_EVERY = 1;

  const boardEl = document.getElementById("board");
  const pointsEl = document.getElementById("board-points");
  const statusEl = document.getElementById("status");
  const restartEl = document.getElementById("restart");
  const winDialog = document.getElementById("win-dialog");
  const loseDialog = document.getElementById("lose-dialog");
  const timerPanel = document.getElementById("timer-panel");
  const timerLabel = document.getElementById("timer-label");
  const timerFill = document.getElementById("timer-fill");
  const welcomeLayer = document.getElementById("welcome-layer");
  const btnStart = document.getElementById("btn-start");
  const winPlayBlack = document.getElementById("win-play-black");
  const winPlayWhite = document.getElementById("win-play-white");
  const recordWinEl = document.getElementById("record-win");
  const recordLossEl = document.getElementById("record-loss");
  const recordDrawEl = document.getElementById("record-draw");
  const boardShellEl = document.getElementById("board-shell");
  const boardSnowEl = document.getElementById("board-snow");
  const boardStarsEl = document.getElementById("board-stars");

  const RECORD_STORAGE_KEY = "gomoku_player_record_v1";
  const WIN_STREAK_STORAGE_KEY = "gomoku_win_streak_v1";
  /** 패배 시 저장한 승리 5연 줄(정규형) — 다음 판 같은 줄 형태 번역 출현 시 막기 우선 */
  const LOSS_LINE_PATTERNS_KEY = "gomoku_ai_loss_win_lines_v1";
  const LOSS_LINE_PATTERNS_MAX = 16;
  /** 사용자가 이기면 true → 다음 resetUi(다음 판)에서 판 외곽 화려 효과 1회 */
  let victoryFrameNextMatch = false;
  /** 다음 판에 쓸 연승 단계 효과 (1~6, 연승이 클수록 화려) */
  let victoryTierForNextMatch = 1;

  /** @type {number[][]} */
  let board;
  let gameOver = false;
  /** 게임 시작 버튼을 누른 뒤에만 true */
  let matchLive = false;
  /** 사용자 돌 색 (흑 또는 백) — 백 선택 시 컴퓨터(흑)가 선공 */
  let humanColor = BLACK;
  /** 사용자가 둘 차례일 때만 true */
  let humanTurn = false;
  /** @type {ReturnType<typeof setInterval> | null} */
  let turnTimerId = null;
  /** @type {ReturnType<typeof setInterval> | null} */
  let aiThinkTickId = null;
  /** @type {ReturnType<typeof setTimeout> | null} */
  let aiPlaceTimeoutId = null;
  /** AI 차례 시작 시각 — 경과 기준으로 제한 시간 표시 */
  let aiTurnStartedAt = 0;
  /** 미니맥스 등으로 aiMove가 겹치지 않게 */
  let aiMoveInProgress = false;
  /** async 미니맥스 양보용 카운터(pickAiMove 시작 시 0으로 리셋) */
  let minimaxSearchTicks = 0;
  /**
   * AI 차례 제한 시간까지의 시각(epoch ms). 이후 미니맥스는 빠져 나와 정적 평가만 사용(착수는 aiMove에서 제한 시간 여부로 결정).
   */
  let aiSearchDeadlineMs = 0;
  /** AI 차례 20초가 끝남(인터벌에서 설정) — 연산 중에도 플래그만 세우고, 끝나면 착수 생략 후 사용자 차례 */
  let aiTurnClockExpired = false;

  function yieldToMainThread() {
    return new Promise((resolve) => setTimeout(resolve, 0));
  }

  function isAiSearchOverTime() {
    return aiSearchDeadlineMs > 0 && Date.now() >= aiSearchDeadlineMs;
  }

  /** runAiTurn에서 시작 시각을 세기 전(aiTurnStartedAt===0)에는 참이 되면 안 됨 — 그렇지 않으면 첫 AI 차례가 즉시 시간 초과 처리됨 */
  function isAiTurnWallClockExceeded() {
    return (
      aiTurnStartedAt > 0 &&
      Date.now() - aiTurnStartedAt >= MOVE_LIMIT_SEC * 1000
    );
  }

  /** 시간 초과 시 즉석 착수용 — 미니맥스 없이 최고 탐욕 후보만 고름 */
  function greedyFallbackPick(ai, human, branchCap) {
    const cap = branchCap ?? AI_MAX_BRANCH;
    const rootMoves = mergeThreatAwareRootMoves(
      ai,
      human,
      orderedMoves(true, ai, human, cap),
      cap
    );
    if (!rootMoves.length) return pickRandomEmpty();
    let bestG = -Infinity;
    let pick = /** @type {[number, number]} */ ([rootMoves[0][0], rootMoves[0][1]]);
    for (const [r, c] of rootMoves) {
      const g = greedyMoveScore(r, c, ai, ai, human);
      if (g > bestG) {
        bestG = g;
        pick = [r, c];
      }
    }
    return pick;
  }
  /** @type {HTMLElement[]} */
  let cells;

  function buildGrid() {
    pointsEl.replaceChildren();
    cells = [];
    board = Array.from({ length: SIZE }, () => Array(SIZE).fill(EMPTY));
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        const btn = document.createElement("button");
        btn.type = "button";
        btn.className = "pt empty";
        btn.dataset.r = String(r);
        btn.dataset.c = String(c);
        btn.style.setProperty("--pr", String(r));
        btn.style.setProperty("--pc", String(c));
        btn.setAttribute("role", "gridcell");
        btn.setAttribute("aria-rowindex", String(r + 1));
        btn.setAttribute("aria-colindex", String(c + 1));
        btn.setAttribute("aria-label", `빈 교차점 ${r + 1}행 ${c + 1}열`);
        pointsEl.appendChild(btn);
        cells.push(btn);
      }
    }
  }

  function idx(r, c) {
    return r * SIZE + c;
  }

  function paintCell(r, c) {
    const el = cells[idx(r, c)];
    const v = board[r][c];
    el.classList.remove("empty", "black", "white");
    if (v === EMPTY) {
      el.classList.add("pt", "empty");
      el.setAttribute("aria-label", `빈 교차점 ${r + 1}행 ${c + 1}열`);
      el.disabled = false;
    } else if (v === BLACK) {
      el.classList.add("pt", "black");
      el.setAttribute("aria-label", `흑 ${r + 1}행 ${c + 1}열`);
      el.disabled = true;
    } else {
      el.classList.add("pt", "white");
      el.setAttribute("aria-label", `백 ${r + 1}행 ${c + 1}열`);
      el.disabled = true;
    }
  }

  function countLine(r, c, dr, dc, player) {
    let n = 0;
    let rr = r + dr;
    let cc = c + dc;
    while (rr >= 0 && rr < SIZE && cc >= 0 && cc < SIZE && board[rr][cc] === player) {
      n++;
      rr += dr;
      cc += dc;
    }
    rr = r - dr;
    cc = c - dc;
    while (rr >= 0 && rr < SIZE && cc >= 0 && cc < SIZE && board[rr][cc] === player) {
      n++;
      rr -= dr;
      cc -= dc;
    }
    return n + 1;
  }

  /** 정확히 5연속만 승 (6목 이상은 승 아님) */
  function isExactFiveWin(r, c, player) {
    const dirs = [
      [0, 1],
      [1, 0],
      [1, 1],
      [1, -1],
    ];
    for (const [dr, dc] of dirs) {
      const line = countLine(r, c, dr, dc, player);
      if (line === 5) return true;
    }
    return false;
  }

  /** 승리한 방향에서 연속 5칸 좌표 (마지막 착수 기준) */
  function collectWinningFive(r, c, player) {
    const dirs = [
      [0, 1],
      [1, 0],
      [1, 1],
      [1, -1],
    ];
    for (const [dr, dc] of dirs) {
      if (countLine(r, c, dr, dc, player) !== 5) continue;
      let rr = r;
      let cc = c;
      while (
        rr - dr >= 0 &&
        rr - dr < SIZE &&
        cc - dc >= 0 &&
        cc - dc < SIZE &&
        board[rr - dr][cc - dc] === player
      ) {
        rr -= dr;
        cc -= dc;
      }
      const out = [];
      for (let i = 0; i < 5; i++) {
        out.push({ r: rr, c: cc });
        rr += dr;
        cc += dc;
      }
      return out;
    }
    return [];
  }

  function highlightWinningFive(r, c, player) {
    for (const { r: rr, c: cc } of collectWinningFive(r, c, player)) {
      cells[idx(rr, cc)].classList.add("win-line");
    }
  }

  /** 보드 위 “가장 마지막 착수” 한 점 — 링 표시용 */
  /** @type {{ r: number; c: number } | null} */
  let lastStonePos = null;

  function clearLastStoneHighlight() {
    if (lastStonePos) {
      const el = cells[idx(lastStonePos.r, lastStonePos.c)];
      if (el) el.classList.remove("last-stone");
    }
    lastStonePos = null;
  }

  function setLastStoneHighlight(r, c) {
    clearLastStoneHighlight();
    lastStonePos = { r, c };
    cells[idx(r, c)].classList.add("last-stone");
  }

  function clearPlacementHistory() {
    clearLastStoneHighlight();
  }

  function stopTurnTimer() {
    if (turnTimerId !== null) {
      clearInterval(turnTimerId);
      turnTimerId = null;
    }
  }

  function stopAiThinkTimer() {
    if (aiThinkTickId !== null) {
      clearInterval(aiThinkTickId);
      aiThinkTickId = null;
    }
    if (aiPlaceTimeoutId !== null) {
      clearTimeout(aiPlaceTimeoutId);
      aiPlaceTimeoutId = null;
    }
  }

  /** AI 차례 타이머 — 실제 경과 시간 기준(연산 중 메인 스레드가 멈춰도 종료 후 표시가 따라잡음) */
  function updateAiCountdownDisplayFromElapsed() {
    if (!timerPanel || !timerLabel || !timerFill || gameOver) return;
    const bar = timerPanel.querySelector(".timer-bar");
    const elapsedSec = Math.floor((Date.now() - aiTurnStartedAt) / 1000);
    const secLeft = Math.max(0, MOVE_LIMIT_SEC - elapsedSec);
    timerPanel.classList.remove("timer-idle");
    timerPanel.classList.add("timer-ai");
    timerLabel.textContent = `${secLeft}초`;
    timerFill.style.opacity = "";
    timerFill.style.width = `${(secLeft / MOVE_LIMIT_SEC) * 100}%`;
    timerPanel.classList.toggle("timer-urgent", secLeft <= 5);
    if (bar) {
      bar.setAttribute("aria-valuenow", String(secLeft));
      bar.setAttribute("aria-valuemax", String(MOVE_LIMIT_SEC));
    }
    return secLeft;
  }

  function updateTimerDisplay(secondsLeft, active) {
    if (!timerPanel || !timerLabel || !timerFill) return;
    const bar = timerPanel.querySelector(".timer-bar");
    if (!active || gameOver) {
      timerPanel.classList.add("timer-idle");
      timerPanel.classList.remove("timer-urgent", "timer-ai");
      timerLabel.textContent = "—";
      timerFill.style.width = "0%";
      timerFill.style.opacity = "";
      if (bar) bar.setAttribute("aria-valuenow", "0");
      return;
    }
    timerPanel.classList.remove("timer-idle", "timer-ai");
    timerLabel.textContent = `${secondsLeft}초`;
    timerFill.style.opacity = "";
    timerFill.style.width = `${(secondsLeft / MOVE_LIMIT_SEC) * 100}%`;
    timerPanel.classList.toggle("timer-urgent", secondsLeft <= 5);
    if (bar) {
      bar.setAttribute("aria-valuenow", String(secondsLeft));
      bar.setAttribute("aria-valuemax", String(MOVE_LIMIT_SEC));
    }
  }

  function startTurnTimer() {
    stopTurnTimer();
    stopAiThinkTimer();
    if (gameOver || !humanTurn) {
      updateTimerDisplay(0, false);
      return;
    }
    let sec = MOVE_LIMIT_SEC;
    updateTimerDisplay(sec, true);
    turnTimerId = setInterval(() => {
      sec -= 1;
      if (sec <= 0) {
        stopTurnTimer();
        onTurnTimeout();
        return;
      }
      updateTimerDisplay(sec, true);
    }, 1000);
  }

  function closeAllDialogs() {
    if (winDialog && winDialog.open) winDialog.close();
    if (loseDialog && loseDialog.open) loseDialog.close();
  }

  const WIN_REVEAL_OVERLAY_CLASS = "win-reveal-overlay";

  function removeWinRevealOverlay() {
    const el = boardEl && boardEl.querySelector(`.${WIN_REVEAL_OVERLAY_CLASS}`);
    if (el) el.remove();
  }

  /**
   * 5연속 하이라이트만 먼저 보여 주고, 판을 누르면 상태 문구·승패 대화상자 표시.
   * @param {() => void} onContinue
   */
  function attachWinRevealOverlay(onContinue) {
    removeWinRevealOverlay();
    if (!boardEl) {
      onContinue();
      return;
    }
    const overlay = document.createElement("button");
    overlay.type = "button";
    overlay.className = WIN_REVEAL_OVERLAY_CLASS;
    overlay.setAttribute(
      "aria-label",
      "5연속으로 끝난 위치를 확인했습니다. 눌러 결과를 표시합니다."
    );
    let done = false;
    const finish = () => {
      if (done) return;
      done = true;
      removeWinRevealOverlay();
      onContinue();
    };
    overlay.addEventListener("click", finish, { once: true });
    boardEl.appendChild(overlay);
    queueMicrotask(() => {
      try {
        overlay.focus({ preventScroll: true });
      } catch (_) {}
    });
  }

  /**
   * @param {string} message
   * @param {{ congratulate?: boolean; condolences?: boolean } & Record<string, unknown>} opt
   */
  function showEndGameDialogs(message, opt) {
    statusEl.textContent = message;
    if (opt.congratulate && winDialog && typeof winDialog.showModal === "function") {
      winDialog.showModal();
    }
    if (opt.condolences && loseDialog && typeof loseDialog.showModal === "function") {
      loseDialog.showModal();
    }
  }

  function loadPlayerRecord() {
    try {
      const raw = localStorage.getItem(RECORD_STORAGE_KEY);
      if (!raw) return { wins: 0, losses: 0, draws: 0 };
      const o = JSON.parse(raw);
      return {
        wins: Number(o.wins) || 0,
        losses: Number(o.losses) || 0,
        draws: Number(o.draws) || 0,
      };
    } catch {
      return { wins: 0, losses: 0, draws: 0 };
    }
  }

  function savePlayerRecord(rec) {
    try {
      localStorage.setItem(RECORD_STORAGE_KEY, JSON.stringify(rec));
    } catch (_) {}
  }

  function refreshRecordDisplay() {
    const r = loadPlayerRecord();
    if (recordWinEl) recordWinEl.textContent = String(r.wins);
    if (recordLossEl) recordLossEl.textContent = String(r.losses);
    if (recordDrawEl) recordDrawEl.textContent = String(r.draws);
  }

  function loadWinStreak() {
    try {
      const v = parseInt(localStorage.getItem(WIN_STREAK_STORAGE_KEY) || "0", 10);
      return Number.isFinite(v) && v >= 0 ? v : 0;
    } catch {
      return 0;
    }
  }

  function saveWinStreak(n) {
    try {
      localStorage.setItem(WIN_STREAK_STORAGE_KEY, String(Math.max(0, n)));
    } catch (_) {}
  }

  function resetWinStreak() {
    saveWinStreak(0);
  }

  /** 다음 판 보상 — 1연승만 격자 안 눈송이 */
  const SNOW_EFFECT_TIER = 1;
  /** 연승 2~(다음 판 단계 ≥2)에서는 별송이 */

  function teardownBoardSnow() {
    if (!boardSnowEl) return;
    boardSnowEl.hidden = true;
    boardSnowEl.replaceChildren();
  }

  function teardownBoardStars() {
    if (!boardStarsEl) return;
    boardStarsEl.hidden = true;
    boardStarsEl.replaceChildren();
  }

  function teardownBoardCelebrationFx() {
    teardownBoardSnow();
    teardownBoardStars();
  }

  /**
   * @param {number} tier 1~6 — 1연승 보상 판에서만 눈송이
   */
  function setupBoardSnowForStreak(tier) {
    if (!boardSnowEl) return;
    if (tier !== SNOW_EFFECT_TIER) {
      teardownBoardSnow();
      return;
    }
    boardSnowEl.replaceChildren();
    const n = Math.min(42 + tier * 14, 130);
    for (let i = 0; i < n; i++) {
      const flake = document.createElement("span");
      flake.className = "snowflake";
      flake.style.setProperty("--x", String(Math.random() * 100));
      flake.style.setProperty("--delay", `${Math.random() * 10}s`);
      flake.style.setProperty("--dur", `${3 + Math.random() * 4}s`);
      flake.style.setProperty("--drift", `${(Math.random() - 0.5) * 42}px`);
      flake.style.setProperty("--size", `${2.5 + Math.random() * 6}px`);
      boardSnowEl.appendChild(flake);
    }
    boardSnowEl.hidden = false;
  }

  /**
   * @param {number} tier 2~6 — 연승 보상 판에서 화려한 별송이
   */
  function setupBoardStarsForStreak(tier) {
    if (!boardStarsEl) return;
    if (tier < 2) {
      teardownBoardStars();
      return;
    }
    boardStarsEl.replaceChildren();
    const n = Math.min(30 + tier * 12, 130);
    for (let i = 0; i < n; i++) {
      const star = document.createElement("span");
      star.className = `starfall starfall--v${1 + Math.floor(Math.random() * 3)}`;
      star.style.setProperty("--x", String(Math.random() * 100));
      star.style.setProperty("--delay", `${Math.random() * 12}s`);
      star.style.setProperty("--dur", `${5.5 + Math.random() * 6}s`);
      star.style.setProperty("--drift", `${(Math.random() - 0.5) * 56}px`);
      star.style.setProperty("--sz", `${5 + Math.random() * 16}px`);
      boardStarsEl.appendChild(star);
    }
    boardStarsEl.hidden = false;
  }

  /** @param {boolean} on @param {number} [tier] 1~6 */
  function setBoardVictoryFrame(on, tier) {
    if (!boardShellEl) return;
    for (let i = 1; i <= 6; i++) {
      boardShellEl.classList.remove(`board-wrap--victory-tier-${i}`);
    }
    boardShellEl.classList.toggle("board-wrap--victory-next", !!on);
    if (on) {
      const t = Number(tier);
      const safe = Number.isFinite(t) ? Math.min(6, Math.max(1, Math.floor(t))) : 1;
      boardShellEl.classList.add(`board-wrap--victory-tier-${safe}`);
    }
  }

  /** @param {"win" | "loss" | "draw"} kind */
  function bumpPlayerRecord(kind) {
    const r = loadPlayerRecord();
    if (kind === "win") r.wins += 1;
    else if (kind === "loss") r.losses += 1;
    else r.draws += 1;
    savePlayerRecord(r);
    refreshRecordDisplay();
  }

  function endGame(message, options) {
    removeWinRevealOverlay();
    setBoardVictoryFrame(false);
    stopTurnTimer();
    stopAiThinkTimer();
    humanTurn = false;
    gameOver = true;
    updateTimerDisplay(0, false);
    const opt = options || {};
    if (opt.congratulate) {
      bumpPlayerRecord("win");
      const nextStreak = loadWinStreak() + 1;
      saveWinStreak(nextStreak);
      victoryTierForNextMatch = Math.min(nextStreak, 6);
      victoryFrameNextMatch = true;
    } else if (opt.condolences) {
      bumpPlayerRecord("loss");
      resetWinStreak();
      teardownBoardCelebrationFx();
    } else {
      bumpPlayerRecord("draw");
      resetWinStreak();
      teardownBoardCelebrationFx();
    }
    if (
      opt.winLine &&
      typeof opt.winR === "number" &&
      typeof opt.winC === "number" &&
      (opt.winPlayer === BLACK || opt.winPlayer === WHITE)
    ) {
      highlightWinningFive(opt.winR, opt.winC, opt.winPlayer);
      if (opt.congratulate && opt.winPlayer === humanColor) {
        rememberAiLossWinningLine(opt.winR, opt.winC, opt.winPlayer);
      }
    }
    for (const el of cells) {
      if (board[+el.dataset.r][+el.dataset.c] === EMPTY) el.disabled = true;
    }

    const deferResultUI =
      (opt.congratulate || opt.condolences) &&
      opt.winLine &&
      typeof opt.winR === "number" &&
      typeof opt.winC === "number" &&
      (opt.winPlayer === BLACK || opt.winPlayer === WHITE);

    if (deferResultUI) {
      statusEl.textContent = opt.congratulate
        ? "5연속 위치를 확인한 뒤, 판을 눌러 주세요."
        : "상대 5연속 위치를 확인한 뒤, 판을 눌러 주세요.";
      attachWinRevealOverlay(() => {
        showEndGameDialogs(message, opt);
      });
      return;
    }

    showEndGameDialogs(message, opt);
  }

  /** 컴퓨터가 잡는 색 (사용자와 반대) */
  function computerColor() {
    return humanColor === BLACK ? WHITE : BLACK;
  }

  function humanColorLabel() {
    return humanColor === BLACK ? "흑" : "백";
  }

  function computerColorLabel() {
    return computerColor() === BLACK ? "흑" : "백";
  }

  function pickRandomEmpty() {
    const empties = [];
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] === EMPTY) empties.push([r, c]);
      }
    }
    if (!empties.length) return null;
    const i = Math.floor(Math.random() * empties.length);
    return empties[i];
  }

  const DIRS = [
    [0, 1],
    [1, 0],
    [1, 1],
    [1, -1],
  ];

  const SC = {
    WIN: 10_000_000,
    OPEN_FOUR: 500_000,
    RUSH_FOUR: 120_000,
    OPEN_THREE: 9_000,
    RUSH_THREE: 2_200,
    OPEN_TWO: 180,
    RUSH_TWO: 45,
    OVERLINE_PEN: 50_000,
    NEIGHBOR_BONUS: 8,
  };

  function inBounds(r, c) {
    return r >= 0 && r < SIZE && c >= 0 && c < SIZE;
  }

  function walkArm(r, c, dr, dc, player) {
    let n = 0;
    let rr = r + dr;
    let cc = c + dc;
    while (inBounds(rr, cc) && board[rr][cc] === player) {
      n++;
      rr += dr;
      cc += dc;
    }
    let beyond = EMPTY;
    if (!inBounds(rr, cc)) beyond = -1;
    else beyond = board[rr][cc];
    return { n, beyond };
  }

  function axisAfterMove(r, c, dr, dc, player) {
    const a = walkArm(r, c, dr, dc, player);
    const b = walkArm(r, c, -dr, -dc, player);
    const total = 1 + a.n + b.n;
    return { total, capA: a.beyond, capB: b.beyond };
  }

  function isCapOpen(cap) {
    return cap === EMPTY;
  }

  function axisScore(ax) {
    const { total, capA, capB } = ax;
    const oa = isCapOpen(capA);
    const ob = isCapOpen(capB);
    const opens = (oa ? 1 : 0) + (ob ? 1 : 0);

    if (total >= 6) return -SC.OVERLINE_PEN;
    if (total === 5) return SC.WIN;

    if (total === 4) {
      if (opens === 2) return SC.OPEN_FOUR;
      if (opens === 1) return SC.RUSH_FOUR;
      return SC.RUSH_FOUR / 6;
    }
    if (total === 3) {
      if (opens === 2) return SC.OPEN_THREE;
      if (opens === 1) return SC.RUSH_THREE;
      return SC.RUSH_THREE / 5;
    }
    if (total === 2) {
      if (opens === 2) return SC.OPEN_TWO;
      if (opens === 1) return SC.RUSH_TWO;
      return SC.RUSH_TWO / 4;
    }
    if (total === 1) {
      if (opens === 2) return SC.OPEN_TWO / 10;
    }
    return 0;
  }

  function evaluateHypothetical(r, c, player) {
    if (board[r][c] !== EMPTY) return -1e15;
    board[r][c] = player;
    let s = 0;
    for (const [dr, dc] of DIRS) {
      s += axisScore(axisAfterMove(r, c, dr, dc, player));
    }
    if (isExactFiveWin(r, c, player)) s = Math.max(s, SC.WIN);
    board[r][c] = EMPTY;
    return s;
  }

  function winsIfPlays(r, c, player) {
    if (board[r][c] !== EMPTY) return false;
    board[r][c] = player;
    const ok = isExactFiveWin(r, c, player);
    board[r][c] = EMPTY;
    return ok;
  }

  /** @param {{ r: number; c: number }[]} cells */
  function normalizeFiveCellPattern(cells) {
    const minR = Math.min(...cells.map((x) => x.r));
    const minC = Math.min(...cells.map((x) => x.c));
    return cells.map(({ r, c }) => ({ r: r - minR, c: c - minC }));
  }

  /** @param {{ r: number; c: number }[]} norm */
  function lossPatternKey(norm) {
    const sorted = [...norm].sort((a, b) => a.r - b.r || a.c - b.c);
    return sorted.map((p) => `${p.r},${p.c}`).join(";");
  }

  /** 가로·세로·대각 직선 5칸을 동일하게 취급하기 위해 90° 회전 정규형을 모두 펼침 */
  function enumerateFiveLineRotationNorms(norm0) {
    /** @type {{ r: number; c: number }[][]} */
    const out = [];
    const keys = new Set();
    let cur = normalizeFiveCellPattern(norm0.map((p) => ({ ...p })));
    for (let i = 0; i < 4; i++) {
      const k = lossPatternKey(cur);
      if (!keys.has(k)) {
        keys.add(k);
        out.push(cur.map((p) => ({ ...p })));
      }
      cur = normalizeFiveCellPattern(cur.map(({ r, c }) => ({ r: -c, c: r })));
    }
    return out;
  }

  function loadLossLinePatterns() {
    try {
      const raw = localStorage.getItem(LOSS_LINE_PATTERNS_KEY);
      if (!raw) return [];
      const arr = JSON.parse(raw);
      return Array.isArray(arr)
        ? arr.filter((x) => x && typeof x.key === "string" && Array.isArray(x.norm))
        : [];
    } catch {
      return [];
    }
  }

  function saveLossLinePatterns(list) {
    try {
      localStorage.setItem(LOSS_LINE_PATTERNS_KEY, JSON.stringify(list.slice(0, LOSS_LINE_PATTERNS_MAX)));
    } catch (_) {}
  }

  /** 사용자(흑/백)가 이긴 직후 판에 남은 5연 줄을 정규형으로 저장 (회전 동형 모두 등록해 다음 판 매칭률↑) */
  function rememberAiLossWinningLine(winR, winC, winner) {
    const cells = collectWinningFive(winR, winC, winner);
    if (cells.length !== 5) return;
    const norm = normalizeFiveCellPattern(cells);
    const variants = enumerateFiveLineRotationNorms(norm);
    let list = loadLossLinePatterns();
    const existingKeys = new Set(list.map((x) => x.key));
    let anyNew = false;
    for (const v of variants) {
      const key = lossPatternKey(v);
      if (existingKeys.has(key)) continue;
      existingKeys.add(key);
      list.unshift({ key, norm: v });
      anyNew = true;
    }
    if (!anyNew) return;
    if (list.length > LOSS_LINE_PATTERNS_MAX) list.length = LOSS_LINE_PATTERNS_MAX;
    saveLossLinePatterns(list);
  }

  /**
   * 저장된 패배 5칸 줄이 판 위에 번역·부분 재현될 때, 그 줄 위 빈 칸 중
   * 상대가 두면 즉승이거나 3·3(이중 위협)이 되는 막점을 고른다.
   * (이전에는 4연+빈1만 봐서 3·3 패배를 같은 줄 형태로 반복할 수 있었음.)
   */
  function findLossMemorizedLineBlock(human) {
    const patterns = loadLossLinePatterns();
    if (!patterns.length) return null;

    /** @type {[number, number] | null} */
    let bestThreatBlock = null;
    let bestThreatEv = -1;

    for (const { norm } of patterns) {
      if (!norm || norm.length !== 5) continue;
      const maxOfsR = Math.max(...norm.map((p) => p.r));
      const maxOfsC = Math.max(...norm.map((p) => p.c));
      for (let dr = -maxOfsR; dr + maxOfsR < SIZE; dr++) {
        for (let dc = -maxOfsC; dc + maxOfsC < SIZE; dc++) {
          let humanCt = 0;
          /** @type {[number, number][]} */
          const empties = [];
          let illegal = false;
          for (const p of norm) {
            const r = dr + p.r;
            const c = dc + p.c;
            if (r < 0 || r >= SIZE || c < 0 || c >= SIZE) {
              illegal = true;
              break;
            }
            const v = board[r][c];
            if (v === human) humanCt++;
            else if (v === EMPTY) empties.push([r, c]);
            else illegal = true;
          }
          if (illegal || !empties.length) continue;
          /* 완전히 빈 5칸만 겹치면 오탐 방지: 그 줄에 상대 돌이 하나도 없으면 스킵 */
          if (humanCt === 0) continue;

          for (const [er, ec] of empties) {
            if (winsIfPlays(er, ec, human)) {
              return [er, ec];
            }
            if (humanMoveFormsDoubleThreat(er, ec, human)) {
              const ev = evaluateHypothetical(er, ec, human);
              if (ev > bestThreatEv) {
                bestThreatEv = ev;
                bestThreatBlock = [er, ec];
              }
            }
          }
        }
      }
    }
    return bestThreatBlock;
  }

  /**
   * 상대가 이 칸에 두면 이중 위협(3·3·4·3·막세 조합 등)인지.
   * 축 최댓값 페어로 4·3을 잡고, 기존 카운트로 나머지 분기를 덮음.
   * 4-4, 3-4, 4-3 패턴 감지 강화
   */
  function humanMoveFormsDoubleThreat(r, c, human) {
    if (board[r][c] !== EMPTY) return false;
    const total = evaluateHypothetical(r, c, human);

    board[r][c] = human;
    /** @type {number[]} */
    const axisScores = [];
    let openThreeAxes = 0;
    let rushThreeAxes = 0;
    let rushFourAxes = 0;
    let openFourAxes = 0;
    for (const [dr, dc] of DIRS) {
      const sc = axisScore(axisAfterMove(r, c, dr, dc, human));
      axisScores.push(sc);
      if (sc >= SC.OPEN_THREE) openThreeAxes++;
      if (sc >= SC.RUSH_THREE) rushThreeAxes++;
      if (sc >= SC.RUSH_FOUR) rushFourAxes++;
      if (sc >= SC.OPEN_FOUR) openFourAxes++;
    }
    board[r][c] = EMPTY;

    axisScores.sort((a, b) => b - a);
    const h0 = axisScores[0];
    const h1 = axisScores[1];
    const h2 = axisScores[2];

    /* 4-4: 열사 두 줄 (가장 위험) */
    if (openFourAxes >= 2) return true;
    /* 4-4: 막세 두 줄도 2수로 막기 불가 */
    if (rushFourAxes >= 2) return true;

    /* 상위 두 축이 모두 열삼 이상 → 3·3 */
    if (h0 >= SC.OPEN_THREE && h1 >= SC.OPEN_THREE) return true;
    /* 막세/열사 + 열삼 → 4·3 계열 (한 수에 수비 불가 분기) */
    if (h0 >= SC.RUSH_FOUR && h1 >= SC.OPEN_THREE) return true;
    if (h0 >= SC.OPEN_FOUR && h1 >= SC.RUSH_THREE) return true;
    if (openFourAxes >= 1 && openThreeAxes >= 1) return true;
    /* 막세 두 줄 + 열삼 한 줄 */
    if (rushThreeAxes >= 2 && openThreeAxes >= 1) return true;

    if (openThreeAxes >= 2) return true;
    if (openThreeAxes >= 1 && rushThreeAxes >= 2) return true;
    if (rushFourAxes >= 1 && rushThreeAxes >= 2) return true;
    /* 한 축 열삼 + 한 축 막세 이상: 합계도 같이 높을 때만 (과막 방지) */
    if (openThreeAxes >= 1 && rushThreeAxes >= 1 && total >= SC.OPEN_THREE + SC.RUSH_THREE - 800) {
      return true;
    }
    /* 상위 세 축이 모두 막세 이상이면 약한 3·3·포크에 근접 */
    if (h0 >= SC.RUSH_THREE && h1 >= SC.RUSH_THREE && h2 >= SC.RUSH_THREE && openThreeAxes >= 1) {
      return true;
    }
    if (total >= SC.OPEN_THREE * 2 + SC.RUSH_THREE) return true;
    if (total >= SC.OPEN_THREE + SC.RUSH_THREE * 2) return true;
    return false;
  }

  /** 빈 칸 중 내 패턴 합 최대 — 공격 우선 판단용 */
  function maxEvaluateHypotheticalForPlayer(player) {
    let best = -Infinity;
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] !== EMPTY) continue;
        const v = evaluateHypothetical(r, c, player);
        if (v > best) best = v;
      }
    }
    return best;
  }

  /** AI가 이 칸에 두면 다음 수에 이길 수 있는지 확인 (2수 이내 승리 경로) */
  function canWinInTwoMoves(r, c, ai) {
    if (board[r][c] !== EMPTY) return false;
    board[r][c] = ai;
    let canWin = false;

    /* 현재 수로 이기는지 확인 */
    if (isExactFiveWin(r, c, ai)) {
      board[r][c] = EMPTY;
      return true;
    }

    /* 다음 AI 수로 이길 수 있는지 확인 */
    for (let rr = 0; rr < SIZE; rr++) {
      for (let cc = 0; cc < SIZE; cc++) {
        if (board[rr][cc] !== EMPTY) continue;
        board[rr][cc] = ai;
        if (isExactFiveWin(rr, cc, ai)) {
          canWin = true;
        }
        board[rr][cc] = EMPTY;
        if (canWin) break;
      }
      if (canWin) break;
    }

    board[r][c] = EMPTY;
    return canWin;
  }

  /** AI가 양쪽 끝이 비어있는 3연(열삼)을 만들 수 있는 수 찾기 */
  function findAiOpenThreeMove(ai, human) {
    let bestMoves = [];
    let bestScore = -Infinity;

    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] !== EMPTY) continue;
        const score = evaluateHypothetical(r, c, ai);

        /* 열삼 이상이면 후보에 추가 */
        if (score >= SC.OPEN_THREE) {
          board[r][c] = ai;
          let hasOpenThree = false;
          for (const [dr, dc] of DIRS) {
            const ax = axisAfterMove(r, c, dr, dc, ai);
            if (ax.total === 3 && ax.capA === EMPTY && ax.capB === EMPTY) {
              hasOpenThree = true;
              break;
            }
          }
          board[r][c] = EMPTY;

          if (hasOpenThree) {
            if (score > bestScore) {
              bestScore = score;
              bestMoves = [[r, c]];
            } else if (score === bestScore) {
              bestMoves.push([r, c]);
            }
          }
        }
      }
    }

    return bestMoves.length > 0 ? bestMoves[0] : null;
  }

  /** 상대가 두 칸에서 형성하는 위협의 타입 평가 (높을수록 위험) */
  function assessDoubleThreatDanger(r, c, human) {
    if (board[r][c] !== EMPTY) return -1e15;
    board[r][c] = human;

    let openFours = 0;
    let rushFours = 0;
    let openThrees = 0;
    let rushThrees = 0;

    for (const [dr, dc] of DIRS) {
      const ax = axisAfterMove(r, c, dr, dc, human);
      const sc = axisScore(ax);
      if (sc >= SC.OPEN_FOUR) openFours++;
      if (sc >= SC.RUSH_FOUR) rushFours++;
      if (sc >= SC.OPEN_THREE) openThrees++;
      if (sc >= SC.RUSH_THREE) rushThrees++;
    }

    board[r][c] = EMPTY;

    /* 위험 레벨 점수 (높을수록 위험) */
    let danger = 0;
    if (openFours >= 2) danger = 10000;  /* 4-4 (열사) */
    else if (rushFours >= 2) danger = 9800;   /* 4-4 (막세) */
    else if (openFours >= 1 && rushFours >= 1) danger = 9600;
    else if (openFours >= 1 && openThrees >= 1) danger = 8000;  /* 4-3 (열사-열삼) */
    else if (openFours >= 1 && rushThrees >= 1) danger = 7800;  /* 4-3 (열사-막삼) */
    else if (rushFours >= 1 && openThrees >= 1) danger = 7600;  /* 4-3 (막세-열삼) */
    else if (rushFours >= 1 && rushThrees >= 1) danger = 7400;  /* 4-3 (막세-막삼) */
    else if (openThrees >= 2) danger = 5000;  /* 3-3 (열삼-열삼) */
    else if (openThrees >= 1 && rushThrees >= 1) danger = 4800;  /* 3-3 (열삼-막삼) */
    else if (rushThrees >= 2) danger = 4600;  /* 3-3 (막삼-막삼) */
    else {
      danger = evaluateHypothetical(r, c, human);
    }

    return danger;
  }

  /** 상대 이중 위협을 막아야 할 칸 중, 위험도 순으로 최우선 차단점 선택 */
  function findHumanDoubleThreatBlockMove(human) {
    let bestRc = /** @type {[number, number] | null} */ (null);
    let bestDanger = -Infinity;
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] !== EMPTY) continue;
        if (!humanMoveFormsDoubleThreat(r, c, human)) continue;
        const danger = assessDoubleThreatDanger(r, c, human);
        if (danger > bestDanger) {
          bestDanger = danger;
          bestRc = [r, c];
        }
      }
    }
    return bestRc;
  }

  function nearestStoneDist(r, c) {
    let best = 99;
    for (let rr = 0; rr < SIZE; rr++) {
      for (let cc = 0; cc < SIZE; cc++) {
        if (board[rr][cc] === EMPTY) continue;
        const d = Math.max(Math.abs(rr - r), Math.abs(cc - c));
        if (d < best) best = d;
      }
    }
    return best;
  }

  /** 인접한 백(본인) 돌 개수 — 연장·포위 공격 유도 */
  function adjacentFriendlyCount(r, c, player) {
    let n = 0;
    for (let dr = -1; dr <= 1; dr++) {
      for (let dc = -1; dc <= 1; dc++) {
        if (dr === 0 && dc === 0) continue;
        const rr = r + dr;
        const cc = c + dc;
        if (inBounds(rr, cc) && board[rr][cc] === player) n++;
      }
    }
    return n;
  }

  function collectCandidates() {
    let hasStone = false;
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] !== EMPTY) {
          hasStone = true;
          break;
        }
      }
      if (hasStone) break;
    }
    const out = [];
    if (!hasStone) {
      for (let r = 0; r < SIZE; r++) {
        for (let c = 0; c < SIZE; c++) {
          if (board[r][c] === EMPTY) out.push([r, c]);
        }
      }
      return out;
    }
    const seen = new Set();
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] === EMPTY) continue;
        for (let dr = -2; dr <= 2; dr++) {
          for (let dc = -2; dc <= 2; dc++) {
            const nr = r + dr;
            const nc = c + dc;
            if (!inBounds(nr, nc) || board[nr][nc] !== EMPTY) continue;
            const key = nr * SIZE + nc;
            if (seen.has(key)) continue;
            seen.add(key);
            out.push([nr, nc]);
          }
        }
      }
    }
    if (!out.length) {
      for (let r = 0; r < SIZE; r++) {
        for (let c = 0; c < SIZE; c++) {
          if (board[r][c] === EMPTY) out.push([r, c]);
        }
      }
    }
    return out;
  }

  /** 정적 평가·후보 정렬 — 탐색이 깊어질수록 평가 구분력이 중요 */
  const HEU = {
    ATT: 2.3,
    DEF: 0.58,
    EXT: 280,
  };

  /** 상대가 이 칸에 두면 패턴 점수가 이 정도면 루트 탐색에 반드시 넣음 (미니맥스 후보 누락 방지) */
  /* 두 열삼이면 합이 대략 2×OPEN_THREE 근처라, 3×으로 두면 3·3 막점이 후보에서 빠졌음 */
  const ROOT_HUMAN_THREAT_MERGE = SC.OPEN_THREE * 2 - 2000;

  /** AI 관점(높을수록 AI 유리) 정적 평가: 주변 후보 칸 휴리스틱 합 */
  function evaluateStaticPosition(ai, human) {
    const cands = collectCandidates();
    let sum = 0;
    for (const [r, c] of cands) {
      if (board[r][c] !== EMPTY) continue;
      const a = evaluateHypothetical(r, c, ai);
      const d = evaluateHypothetical(r, c, human);
      let s = a * HEU.ATT + d * HEU.DEF;
      s += adjacentFriendlyCount(r, c, ai) * HEU.EXT;
      const nd = nearestStoneDist(r, c);
      if (nd < 99) s += (4 - Math.min(nd, 4)) * SC.NEIGHBOR_BONUS;
      sum += s;
    }
    return sum;
  }

  /** 되는 쪽이 두는 수 기준 단일 수 점수 — 정렬용 */
  function greedyMoveScore(r, c, mover, ai, human) {
    const opp = mover === ai ? human : ai;
    const attack = evaluateHypothetical(r, c, mover);
    const defense = evaluateHypothetical(r, c, opp);
    let s = attack * HEU.ATT + defense * HEU.DEF;
    s += adjacentFriendlyCount(r, c, mover) * HEU.EXT;
    const nd = nearestStoneDist(r, c);
    if (nd < 99) s += (4 - Math.min(nd, 4)) * SC.NEIGHBOR_BONUS;
    /* AI 차례: 공격 패턴 후보가 정렬·루트 상단으로 오도록 가산 */
    if (mover === ai) {
      if (attack >= SC.RUSH_FOUR) {
        s += attack * 0.045;
      } else if (attack >= SC.OPEN_THREE) {
        s += attack * 0.028;
      } else if (attack >= SC.RUSH_THREE) {
        s += attack * 0.014;
      } else if (attack >= SC.OPEN_TWO) {
        s += attack * 0.005;
      }
    }
    return s;
  }

  /** 탐색 후보 — 중앙만 남기면 변·모서리의 필수 막수가 제외되어 동일 패턴으로 자주 패배함 */
  function collectCandidatesForSearch() {
    return collectCandidates().filter(([r, c]) => board[r][c] === EMPTY);
  }

  function boardStoneCount() {
    let n = 0;
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] !== EMPTY) n++;
      }
    }
    return n;
  }

  /** 초반은 후보 좁혀 속도 유지, 중반 이후는 상한(AI_SEARCH_PLIES)까지 읽기 */
  function effectiveSearchDepthPlies() {
    const n = boardStoneCount();
    if (n <= 6) return 3;
    if (n >= 40) return 2;
    return 3;
  }

  function effectiveMaxBranch() {
    const n = boardStoneCount();
    if (n <= 6) return 12;
    if (n >= 40) return 12;
    return 14;
  }

  /**
   * 루트 착수 후보에 ‘상대가 두기 좋은 강한 칸’을 꼭 넣고 다시 정렬해 상한만 자름.
   * @param {number} ai
   * @param {number} human
   * @param {[number, number][]} baseMoves
   * @param {number} [branchCap]
   */
  function mergeThreatAwareRootMoves(ai, human, baseMoves, branchCap) {
    const seen = new Set(baseMoves.map(([r, c]) => r * SIZE + c));
    const extras = [];
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] !== EMPTY) continue;
        const key = r * SIZE + c;
        if (seen.has(key)) continue;
        const humScore = evaluateHypothetical(r, c, human);
        if (
          humScore >= ROOT_HUMAN_THREAT_MERGE ||
          winsIfPlays(r, c, human) ||
          humanMoveFormsDoubleThreat(r, c, human)
        ) {
          extras.push([r, c]);
          seen.add(key);
        }
      }
    }
    if (!extras.length) return baseMoves;
    const merged = [...extras, ...baseMoves];
    const scored = merged.map(([r, c]) => ({
      r,
      c,
      s: greedyMoveScore(r, c, ai, ai, human),
    }));
    scored.sort((a, b) => b.s - a.s);
    const out = [];
    const cap = branchCap ?? AI_MAX_BRANCH;
    for (let i = 0; i < scored.length && i < cap; i++) {
      out.push([scored[i].r, scored[i].c]);
    }
    return out;
  }

  /**
   * @param {boolean} forMax - true: AI 차례(큰 수부터), false: 사용자 차례(강한 응수부터)
   */
  function orderedMoves(forMax, ai, human, maxBranch) {
    const cap = maxBranch ?? AI_MAX_BRANCH;
    const mover = forMax ? ai : human;
    const raw = collectCandidatesForSearch();
    const scored = [];
    for (const [r, c] of raw) {
      if (board[r][c] !== EMPTY) continue;
      scored.push({ r, c, s: greedyMoveScore(r, c, mover, ai, human) });
    }
    scored.sort((a, b) => b.s - a.s);
    const out = [];
    for (let i = 0; i < scored.length && i < cap; i++) {
      out.push([scored[i].r, scored[i].c]);
    }
    return out;
  }

  /**
   * 미니맥스 + 알파-베타. aiToMove: 이번에 둘 색이 AI이면 true.
   * 반환: AI 관점 점수(클수록 AI 유리).
   * 주기적으로 await로 양보해 타이머 등 UI가 멈추지 않게 함.
   */
  async function minimax(depth, aiToMove, alpha, beta, ai, human, maxBranch) {
    minimaxSearchTicks++;
    if (minimaxSearchTicks % MINIMAX_YIELD_EVERY === 0) {
      await yieldToMainThread();
    }

    if (isAiSearchOverTime()) {
      return evaluateStaticPosition(ai, human);
    }

    if (depth === 0) return evaluateStaticPosition(ai, human);

    const branch = maxBranch ?? AI_MAX_BRANCH;
    const moves = orderedMoves(aiToMove, ai, human, branch);
    if (!moves.length) return evaluateStaticPosition(ai, human);

    if (aiToMove) {
      let best = -AI_EVAL_WIN;
      for (const [r, c] of moves) {
        if (isAiSearchOverTime()) {
          return evaluateStaticPosition(ai, human);
        }
        if (board[r][c] !== EMPTY) continue;
        board[r][c] = ai;
        let v;
        if (isExactFiveWin(r, c, ai)) {
          v = AI_EVAL_WIN;
        } else {
          v = await minimax(depth - 1, false, alpha, beta, ai, human, branch);
        }
        board[r][c] = EMPTY;
        best = Math.max(best, v);
        alpha = Math.max(alpha, best);
        if (beta <= alpha) break;
      }
      return best;
    }

    let best = AI_EVAL_WIN;
    for (const [r, c] of moves) {
      if (isAiSearchOverTime()) {
        return evaluateStaticPosition(ai, human);
      }
      if (board[r][c] !== EMPTY) continue;
      board[r][c] = human;
      let v;
      if (isExactFiveWin(r, c, human)) {
        v = -AI_EVAL_WIN;
      } else {
        v = await minimax(depth - 1, true, alpha, beta, ai, human, branch);
      }
      board[r][c] = EMPTY;
      best = Math.min(best, v);
      beta = Math.min(beta, best);
      if (beta <= alpha) break;
    }
    return best;
  }

  async function pickAiMove() {
    const candidates = collectCandidates();
    if (!candidates.length) return null;

    const ai = computerColor();
    const human = humanColor;
    const center = (SIZE - 1) / 2;

    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] !== EMPTY) continue;
        if (winsIfPlays(r, c, ai)) return [r, c];
      }
    }

    /* 2수 이내 승리 경로 찾기 (명확한 승리 의도) */
    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] !== EMPTY) continue;
        if (canWinInTwoMoves(r, c, ai)) return [r, c];
      }
    }

    for (let r = 0; r < SIZE; r++) {
      for (let c = 0; c < SIZE; c++) {
        if (board[r][c] !== EMPTY) continue;
        if (winsIfPlays(r, c, human)) return [r, c];
      }
    }

    /* 지난 패에서 진 줄·3·3 형태 재현 시, 공격보다 우선 막음 (동일 패턴 반복 패배 방지) */
    const lossMemBlock = findLossMemorizedLineBlock(human);
    if (lossMemBlock) {
      return lossMemBlock;
    }

    const blockDouble = findHumanDoubleThreatBlockMove(human);
    /*
     * 3·3·4·3 등은 한 수로 막아야 하므로, AI가 막 세(열사)를 노리고 있어도 이중위협 막기를 우선함.
     * 즉승은 위에서 이미 처리됨.
     */
    if (blockDouble) {
      return blockDouble;
    }

    /* 공격적으로 양쪽 끝이 비어있는 3연(열삼) 구축 시도 */
    const openThreeMove = findAiOpenThreeMove(ai, human);
    if (openThreeMove) {
      return openThreeMove;
    }

    const stones = boardStoneCount();
    /* 빈 판: 후보 361칸×미니맥스로 수 초 걸림 → 천원 즉시 */
    if (stones === 0) {
      const c = (SIZE - 1) >> 1;
      return [c, c];
    }
    /* 초반 3수: 미니맥스 대신 탐욕만(후보 영역도 작음) */
    if (stones <= 4) {
      const branchCap = effectiveMaxBranch();
      return greedyFallbackPick(ai, human, branchCap);
    }

    const branchCap = effectiveMaxBranch();
    const depthPlies = effectiveSearchDepthPlies();
    const rootMoves = mergeThreatAwareRootMoves(
      ai,
      human,
      orderedMoves(true, ai, human, branchCap),
      branchCap
    );
    if (!rootMoves.length) return pickRandomEmpty();

    minimaxSearchTicks = 0;

    let bestVal = -Infinity;
    let picks = [];
    const maxRootEvals = Math.min(rootMoves.length, 8);

    for (let idx = 0; idx < maxRootEvals; idx++) {
      if (isAiSearchOverTime()) {
        break;
      }
      const [r, c] = rootMoves[idx];
      await yieldToMainThread();
      if (board[r][c] !== EMPTY) continue;
      board[r][c] = ai;
      let v;
      if (isExactFiveWin(r, c, ai)) {
        board[r][c] = EMPTY;
        return [r, c];
      }
      v = await minimax(
        depthPlies - 1,
        false,
        -AI_EVAL_WIN,
        AI_EVAL_WIN,
        ai,
        human,
        branchCap
      );
      board[r][c] = EMPTY;

      if (v > bestVal) {
        bestVal = v;
        picks = [[r, c]];
      } else if (v === bestVal) {
        picks.push([r, c]);
      }
    }

    if (!picks.length) {
      return greedyFallbackPick(ai, human, branchCap);
    }

    picks.sort((a, b) => {
      const ga = greedyMoveScore(a[0], a[1], ai, ai, human);
      const gb = greedyMoveScore(b[0], b[1], ai, ai, human);
      if (gb !== ga) return gb - ga;
      const da = Math.abs(a[0] - center) + Math.abs(a[1] - center);
      const db = Math.abs(b[0] - center) + Math.abs(b[1] - center);
      if (da !== db) return da - db;
      if (a[0] !== b[0]) return a[0] - b[0];
      return a[1] - b[1];
    });
    return picks[0] || null;
  }

  async function aiMove() {
    if (!matchLive || gameOver || aiMoveInProgress) return;
    aiMoveInProgress = true;
    try {
      const rawPick = await pickAiMove();
      /** 미니맥스 등 동기 연산 후 남은 시간 표시 맞춤 */
      updateAiCountdownDisplayFromElapsed();
      stopAiThinkTimer();

      const aiOverTime = aiTurnClockExpired || isAiTurnWallClockExceeded();

      if (aiOverTime) {
        statusEl.textContent = `컴퓨터 연산 시간 초과 — 당신의 차례입니다 (${humanColorLabel()})`;
        humanTurn = true;
        for (const el of cells) {
          if (board[+el.dataset.r][+el.dataset.c] === EMPTY) el.disabled = false;
        }
        startTurnTimer();
        return;
      }

      const pick = rawPick ?? pickRandomEmpty();

      if (!pick) {
        endGame("무승부 (판 가득 참)");
        return;
      }
      const [r, c] = pick;
      const ai = computerColor();
      board[r][c] = ai;
      paintCell(r, c);
      setLastStoneHighlight(r, c);
      if (isExactFiveWin(r, c, ai)) {
        const w = computerColorLabel();
        endGame(`패배했습니다 (${w}이 5연속).`, {
          condolences: true,
          winLine: true,
          winR: r,
          winC: c,
          winPlayer: ai,
        });
        return;
      }
      if (!pickRandomEmpty()) {
        endGame("무승부 (판 가득 참)");
        return;
      }
      statusEl.textContent = `당신의 차례입니다 (${humanColorLabel()})`;
      humanTurn = true;
      for (const el of cells) {
        if (board[+el.dataset.r][+el.dataset.c] === EMPTY) el.disabled = false;
      }
      startTurnTimer();
    } finally {
      aiMoveInProgress = false;
      aiSearchDeadlineMs = 0;
      aiTurnClockExpired = false;
    }
  }

  /**
   * AI 차례: 사용자와 동일하게 20초 제한 시간이 줄어듦(경과 시간 기준).
   * 짧은 지연 뒤 착수 계산 — 그전에도 인터벌로 막대가 갱신됨.
   */
  function runAiTurn() {
    stopTurnTimer();
    stopAiThinkTimer();
    aiTurnClockExpired = false;
    aiTurnStartedAt = Date.now();
    aiSearchDeadlineMs = aiTurnStartedAt + MOVE_LIMIT_SEC * 1000 - 80;

    statusEl.textContent = `컴퓨터(${computerColorLabel()})가 두는 중…`;
    for (const el of cells) {
      if (board[+el.dataset.r][+el.dataset.c] === EMPTY) el.disabled = true;
    }

    updateAiCountdownDisplayFromElapsed();
    aiThinkTickId = window.setInterval(() => {
      if (gameOver) {
        stopAiThinkTimer();
        return;
      }
      const left = updateAiCountdownDisplayFromElapsed();
      if (left <= 0) {
        aiTurnClockExpired = true;
        aiSearchDeadlineMs = Date.now();
        stopAiThinkTimer();
        if (aiPlaceTimeoutId !== null) {
          clearTimeout(aiPlaceTimeoutId);
          aiPlaceTimeoutId = null;
        }
      }
    }, 100);

    const jitter =
      AI_THINK_JITTER_MIN_MS +
      Math.random() * (AI_THINK_JITTER_MAX_MS - AI_THINK_JITTER_MIN_MS);

    window.requestAnimationFrame(() => {
      window.requestAnimationFrame(() => {
        aiPlaceTimeoutId = window.setTimeout(() => {
          aiPlaceTimeoutId = null;
          if (gameOver) return;
          aiMove().catch((err) => console.error("AI move error:", err));
        }, jitter);
      });
    });
  }

  function onTurnTimeout() {
    if (!matchLive || gameOver || !humanTurn) return;
    humanTurn = false;
    stopTurnTimer();
    stopAiThinkTimer();
    updateTimerDisplay(0, false);
    statusEl.textContent =
      humanColor === BLACK
        ? "시간 초과 — 흑 착수 없음, 백이 둡니다."
        : "시간 초과 — 백 착수 없음, 흑이 둡니다.";
    runAiTurn();
  }

  function onBoardClick(e) {
    if (!matchLive || gameOver || !humanTurn) return;
    const btn = e.target.closest(".pt");
    if (!btn || btn.disabled) return;
    const r = +btn.dataset.r;
    const c = +btn.dataset.c;
    if (board[r][c] !== EMPTY) return;

    humanTurn = false;
    stopTurnTimer();
    stopAiThinkTimer();
    updateTimerDisplay(0, false);

    board[r][c] = humanColor;
    paintCell(r, c);
    setLastStoneHighlight(r, c);

    if (isExactFiveWin(r, c, humanColor)) {
      endGame(`승리! ${humanColorLabel()} 5연속입니다.`, {
        congratulate: true,
        winLine: true,
        winR: r,
        winC: c,
        winPlayer: humanColor,
      });
      return;
    }

    if (!pickRandomEmpty()) {
      endGame("무승부 (판 가득 참)");
      return;
    }

    runAiTurn();
  }

  function resetUi() {
    removeWinRevealOverlay();
    closeAllDialogs();
    stopTurnTimer();
    stopAiThinkTimer();
    gameOver = false;
    matchLive = true;
    if (welcomeLayer) welcomeLayer.hidden = true;
    buildGrid();
    clearPlacementHistory();
    if (restartEl) restartEl.disabled = false;

    if (victoryFrameNextMatch) {
      const tier = victoryTierForNextMatch;
      setBoardVictoryFrame(true, tier);
      victoryFrameNextMatch = false;
      if (tier >= 2) {
        teardownBoardSnow();
        setupBoardStarsForStreak(tier);
      } else {
        teardownBoardStars();
        setupBoardSnowForStreak(tier);
      }
    } else {
      setBoardVictoryFrame(false);
      teardownBoardCelebrationFx();
    }

    if (humanColor === BLACK) {
      statusEl.textContent = "당신의 차례입니다 (흑)";
      humanTurn = true;
      for (const el of cells) {
        if (board[+el.dataset.r][+el.dataset.c] === EMPTY) el.disabled = false;
      }
      startTurnTimer();
    } else {
      humanTurn = false;
      statusEl.textContent = `컴퓨터(${computerColorLabel()})가 선공입니다…`;
      for (const el of cells) {
        if (board[+el.dataset.r][+el.dataset.c] === EMPTY) el.disabled = true;
      }
      updateTimerDisplay(0, false);
      runAiTurn();
    }
  }

  function initPreGame() {
    removeWinRevealOverlay();
    closeAllDialogs();
    stopTurnTimer();
    stopAiThinkTimer();
    matchLive = false;
    humanTurn = false;
    humanColor = BLACK;
    gameOver = false;
    victoryFrameNextMatch = false;
    setBoardVictoryFrame(false);
    teardownBoardCelebrationFx();
    buildGrid();
    clearPlacementHistory();
    statusEl.textContent = "게임 시작 버튼을 눌러 주세요.";
    updateTimerDisplay(0, false);
    if (welcomeLayer) welcomeLayer.hidden = false;
    if (restartEl) restartEl.disabled = true;
    for (const el of cells) el.disabled = true;
    if (btnStart) btnStart.focus();
  }

  pointsEl.addEventListener("click", onBoardClick);
  restartEl.addEventListener("click", () => {
    humanColor = BLACK;
    /** 직전 판 승리 시 `endGame`에서 켠 `victoryFrameNextMatch`를 유지 → 다음 `resetUi`에서 바둑판 보상 효과 1회 */
    resetWinStreak();
    resetUi();
  });
  if (btnStart)
    btnStart.addEventListener("click", () => {
      humanColor = BLACK;
      victoryFrameNextMatch = false;
      resetWinStreak();
      resetUi();
    });

  if (winPlayBlack)
    winPlayBlack.addEventListener("click", () => {
      humanColor = BLACK;
      if (winDialog && winDialog.open) winDialog.close();
      resetUi();
    });
  if (winPlayWhite)
    winPlayWhite.addEventListener("click", () => {
      humanColor = WHITE;
      if (winDialog && winDialog.open) winDialog.close();
      resetUi();
    });

  refreshRecordDisplay();
  initPreGame();
})();
