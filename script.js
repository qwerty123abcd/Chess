/* ============================================================
   ENDGAME — a small, self-contained chess implementation.
   Board convention: row 0 = rank 8 (top), row 7 = rank 1 (bottom).
                      col 0 = file a,      col 7 = file h.
   ============================================================ */

import { initializeApp } from "https://www.gstatic.com/firebasejs/12.8.0/firebase-app.js";
import {
  getFirestore, doc, getDoc, setDoc, updateDoc, onSnapshot,
  collection, query, orderBy, limit, increment, serverTimestamp
} from "https://www.gstatic.com/firebasejs/12.8.0/firebase-firestore.js";

const firebaseConfig = {
  apiKey: "AIzaSyAlK-tULhM2KG_kFweHbbr7-KKWZ1rwFsQ",
  authDomain: "chess-fa228.firebaseapp.com",
  projectId: "chess-fa228",
  storageBucket: "chess-fa228.firebasestorage.app",
  messagingSenderId: "987094390034",
  appId: "1:987094390034:web:62f7ffa53c569c33ef4fcb",
  measurementId: "G-CQVRMTNV7Q"
};

const fbApp = initializeApp(firebaseConfig);
const db = getFirestore(fbApp);

const FILES = ['a','b','c','d','e','f','g','h'];

const UNICODE = {
  w: { p:'♙', n:'♘', b:'♗', r:'♖', q:'♕', k:'♔' },
  b: { p:'♟', n:'♞', b:'♝', r:'♜', q:'♛', k:'♚' }
};

const PIECE_VALUE = { p:100, n:320, b:330, r:500, q:900, k:20000 };

const KNIGHT_OFFSETS = [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]];
const KING_OFFSETS   = [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]];
const ROOK_DIRS      = [[-1,0],[1,0],[0,-1],[0,1]];
const BISHOP_DIRS    = [[-1,-1],[-1,1],[1,-1],[1,1]];

function inBounds(r,c){ return r>=0 && r<8 && c>=0 && c<8; }
function sq(r,c){ return FILES[c] + (8-r); }

function cloneBoard(board){
  return board.map(row => row.map(cell => cell ? {...cell} : null));
}

function freshBoard(){
  const back = ['r','n','b','q','k','b','n','r'];
  const board = Array.from({length:8}, () => Array(8).fill(null));
  for(let c=0;c<8;c++){
    board[0][c] = { type: back[c], color: 'b' };
    board[1][c] = { type: 'p', color: 'b' };
    board[6][c] = { type: 'p', color: 'w' };
    board[7][c] = { type: back[c], color: 'w' };
  }
  return board;
}

/* ---------------- Game state ---------------- */

let game = null;

function newGame(opts = {}){
  const prev = game;
  clearTimeout(botTimer);
  clearTimeout(overTimer);
  game = {
    board: freshBoard(),
    turn: 'w',
    castling: { wK:true, wQ:true, bK:true, bQ:true },
    enPassant: null,        // {r,c} square a pawn could capture into
    history: [],            // list of {move, notation, snapshotBefore}
    capturedByWhite: [],     // black pieces white has taken
    capturedByBlack: [],     // white pieces black has taken
    over: false,
    result: null,
    winner: null,            // 'w' | 'b' | 'draw' | null
    endReason: null,         // 'checkmate' | 'stalemate' | 'resign'
    overShown: false,
    lastMove: null,
    flipped: false,
    mode: opts.mode || (prev ? prev.mode : 'two-player'),
    difficulty: opts.difficulty || (prev ? prev.difficulty : 'medium'),
    humanColor: opts.humanColor || (prev ? prev.humanColor : 'w'),
    selected: null,
    legalMovesForSelected: []
  };
  if(game.mode === 'computer' && game.humanColor === 'b') game.flipped = true;
  render();
  updateStatus();
}

let botTimer = null;
let overTimer = null;

function botColor(){ return game.humanColor === 'w' ? 'b' : 'w'; }

/* ---------------- Attack / check detection ---------------- */

function isSquareAttacked(board, r, c, byColor){
  const pawnDir = byColor === 'w' ? 1 : -1;
  for(const dc of [-1,1]){
    const pr = r + pawnDir, pc = c + dc;
    if(inBounds(pr,pc)){
      const p = board[pr][pc];
      if(p && p.color === byColor && p.type === 'p') return true;
    }
  }
  for(const [dr,dc] of KNIGHT_OFFSETS){
    const nr=r+dr, nc=c+dc;
    if(inBounds(nr,nc)){
      const p = board[nr][nc];
      if(p && p.color === byColor && p.type === 'n') return true;
    }
  }
  for(const [dr,dc] of KING_OFFSETS){
    const nr=r+dr, nc=c+dc;
    if(inBounds(nr,nc)){
      const p = board[nr][nc];
      if(p && p.color === byColor && p.type === 'k') return true;
    }
  }
  for(const [dr,dc] of ROOK_DIRS){
    let nr=r+dr, nc=c+dc;
    while(inBounds(nr,nc)){
      const p = board[nr][nc];
      if(p){
        if(p.color === byColor && (p.type==='r' || p.type==='q')) return true;
        break;
      }
      nr+=dr; nc+=dc;
    }
  }
  for(const [dr,dc] of BISHOP_DIRS){
    let nr=r+dr, nc=c+dc;
    while(inBounds(nr,nc)){
      const p = board[nr][nc];
      if(p){
        if(p.color === byColor && (p.type==='b' || p.type==='q')) return true;
        break;
      }
      nr+=dr; nc+=dc;
    }
  }
  return false;
}

function findKing(board, color){
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(p && p.color===color && p.type==='k') return {r,c};
  }
  return null;
}

function inCheck(board, color){
  const k = findKing(board, color);
  if(!k) return false;
  return isSquareAttacked(board, k.r, k.c, color==='w' ? 'b' : 'w');
}

/* ---------------- Pseudo-legal move generation ---------------- */

function generatePieceMoves(board, r, c, state){
  const piece = board[r][c];
  if(!piece) return [];
  const moves = [];
  const color = piece.color;
  const enemy = color === 'w' ? 'b' : 'w';

  const addSlide = (dirs) => {
    for(const [dr,dc] of dirs){
      let nr=r+dr, nc=c+dc;
      while(inBounds(nr,nc)){
        const target = board[nr][nc];
        if(!target){
          moves.push({ from:{r,c}, to:{r:nr,c:nc} });
        } else {
          if(target.color === enemy) moves.push({ from:{r,c}, to:{r:nr,c:nc}, capture:true });
          break;
        }
        nr+=dr; nc+=dc;
      }
    }
  };

  if(piece.type === 'p'){
    const dir = color === 'w' ? -1 : 1;
    const startRow = color === 'w' ? 6 : 1;
    const promoRow = color === 'w' ? 0 : 7;
    const oneR = r+dir;
    if(inBounds(oneR,c) && !board[oneR][c]){
      if(oneR === promoRow){
        for(const promo of ['q','r','b','n']) moves.push({from:{r,c}, to:{r:oneR,c}, promotion:promo});
      } else {
        moves.push({from:{r,c}, to:{r:oneR,c}});
        const twoR = r+dir*2;
        if(r===startRow && !board[twoR][c]){
          moves.push({from:{r,c}, to:{r:twoR,c}, doubleStep:true});
        }
      }
    }
    for(const dc of [-1,1]){
      const nr=r+dir, nc=c+dc;
      if(!inBounds(nr,nc)) continue;
      const target = board[nr][nc];
      if(target && target.color===enemy){
        if(nr===promoRow){
          for(const promo of ['q','r','b','n']) moves.push({from:{r,c}, to:{r:nr,c:nc}, capture:true, promotion:promo});
        } else {
          moves.push({from:{r,c}, to:{r:nr,c:nc}, capture:true});
        }
      } else if(state.enPassant && state.enPassant.r===nr && state.enPassant.c===nc){
        moves.push({from:{r,c}, to:{r:nr,c:nc}, capture:true, enPassant:true});
      }
    }
  }
  else if(piece.type === 'n'){
    for(const [dr,dc] of KNIGHT_OFFSETS){
      const nr=r+dr, nc=c+dc;
      if(!inBounds(nr,nc)) continue;
      const target = board[nr][nc];
      if(!target) moves.push({from:{r,c}, to:{r:nr,c:nc}});
      else if(target.color===enemy) moves.push({from:{r,c}, to:{r:nr,c:nc}, capture:true});
    }
  }
  else if(piece.type === 'b'){ addSlide(BISHOP_DIRS); }
  else if(piece.type === 'r'){ addSlide(ROOK_DIRS); }
  else if(piece.type === 'q'){ addSlide(ROOK_DIRS); addSlide(BISHOP_DIRS); }
  else if(piece.type === 'k'){
    for(const [dr,dc] of KING_OFFSETS){
      const nr=r+dr, nc=c+dc;
      if(!inBounds(nr,nc)) continue;
      const target = board[nr][nc];
      if(!target) moves.push({from:{r,c}, to:{r:nr,c:nc}});
      else if(target.color===enemy) moves.push({from:{r,c}, to:{r:nr,c:nc}, capture:true});
    }
    // Castling
    const enemyColor = enemy;
    const rights = state.castling;
    const homeRow = color==='w' ? 7 : 0;
    if(r===homeRow && c===4 && !inCheck(board,color)){
      const kingSideRight = color==='w' ? rights.wK : rights.bK;
      const queenSideRight = color==='w' ? rights.wQ : rights.bQ;
      if(kingSideRight && !board[homeRow][5] && !board[homeRow][6] &&
         board[homeRow][7] && board[homeRow][7].type==='r' && board[homeRow][7].color===color &&
         !isSquareAttacked(board, homeRow, 5, enemyColor) &&
         !isSquareAttacked(board, homeRow, 6, enemyColor)){
        moves.push({from:{r,c}, to:{r:homeRow,c:6}, castle:'K'});
      }
      if(queenSideRight && !board[homeRow][3] && !board[homeRow][2] && !board[homeRow][1] &&
         board[homeRow][0] && board[homeRow][0].type==='r' && board[homeRow][0].color===color &&
         !isSquareAttacked(board, homeRow, 3, enemyColor) &&
         !isSquareAttacked(board, homeRow, 2, enemyColor)){
        moves.push({from:{r,c}, to:{r:homeRow,c:2}, castle:'Q'});
      }
    }
  }
  return moves;
}

function generateAllMoves(board, color, state){
  let moves = [];
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(p && p.color===color) moves.push(...generatePieceMoves(board,r,c,state));
  }
  return moves;
}

/* Apply a move to a board+state pair, returning nothing (mutates copies passed in) */
function applyMove(board, state, move){
  const piece = board[move.from.r][move.from.c];
  const color = piece.color;
  let captured = null;

  if(move.enPassant){
    const capRow = move.from.r;
    const capCol = move.to.c;
    captured = board[capRow][capCol];
    board[capRow][capCol] = null;
  } else if(board[move.to.r][move.to.c]){
    captured = board[move.to.r][move.to.c];
  }

  board[move.to.r][move.to.c] = { type: move.promotion || piece.type, color };
  board[move.from.r][move.from.c] = null;

  if(move.castle){
    const homeRow = move.from.r;
    if(move.castle === 'K'){
      board[homeRow][5] = board[homeRow][7];
      board[homeRow][7] = null;
    } else {
      board[homeRow][3] = board[homeRow][0];
      board[homeRow][0] = null;
    }
  }

  // update castling rights
  if(piece.type === 'k'){
    if(color==='w'){ state.castling.wK=false; state.castling.wQ=false; }
    else { state.castling.bK=false; state.castling.bQ=false; }
  }
  if(piece.type === 'r'){
    if(color==='w' && move.from.r===7 && move.from.c===0) state.castling.wQ=false;
    if(color==='w' && move.from.r===7 && move.from.c===7) state.castling.wK=false;
    if(color==='b' && move.from.r===0 && move.from.c===0) state.castling.bQ=false;
    if(color==='b' && move.from.r===0 && move.from.c===7) state.castling.bK=false;
  }
  if(captured && captured.type==='r'){
    if(move.to.r===7 && move.to.c===0) state.castling.wQ=false;
    if(move.to.r===7 && move.to.c===7) state.castling.wK=false;
    if(move.to.r===0 && move.to.c===0) state.castling.bQ=false;
    if(move.to.r===0 && move.to.c===7) state.castling.bK=false;
  }

  // update en passant target
  if(move.doubleStep){
    const midRow = (move.from.r + move.to.r) / 2;
    state.enPassant = { r: midRow, c: move.from.c };
  } else {
    state.enPassant = null;
  }

  return captured;
}

/* Legal moves = pseudo moves that don't leave own king in check */
function legalMovesFrom(r,c){
  const board = game.board;
  const piece = board[r][c];
  if(!piece || piece.color !== game.turn) return [];
  const pseudo = generatePieceMoves(board, r, c, game);
  const legal = [];
  for(const move of pseudo){
    const b2 = cloneBoard(board);
    const s2 = { castling: {...game.castling}, enPassant: game.enPassant };
    applyMove(b2, s2, move);
    if(!inCheck(b2, piece.color)) legal.push(move);
  }
  return legal;
}

function allLegalMoves(color){
  const board = game.board;
  let moves = [];
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(p && p.color===color){
      const pseudo = generatePieceMoves(board, r, c, game);
      for(const move of pseudo){
        const b2 = cloneBoard(board);
        const s2 = { castling: {...game.castling}, enPassant: game.enPassant };
        applyMove(b2, s2, move);
        if(!inCheck(b2, color)) moves.push(move);
      }
    }
  }
  return moves;
}

/* ---------------- Notation ---------------- */

function moveNotation(move, piece, wasCapture, checkChar){
  if(move.castle === 'K') return 'O-O' + checkChar;
  if(move.castle === 'Q') return 'O-O-O' + checkChar;
  const files = 'abcdefgh';
  let s = '';
  if(piece.type !== 'p'){
    s += piece.type.toUpperCase();
    if(wasCapture) s += 'x';
  } else if(wasCapture){
    s += files[move.from.c] + 'x';
  }
  s += sq(move.to.r, move.to.c);
  if(move.promotion) s += '=' + move.promotion.toUpperCase();
  s += checkChar;
  return s;
}

/* ---------------- Making a real move on the live game ---------------- */

function playMove(move){
  const board = game.board;
  const piece = board[move.from.r][move.from.c];
  const color = piece.color;
  const wasCapture = !!move.capture || !!board[move.to.r][move.to.c];

  const snapshot = {
    board: cloneBoard(board),
    turn: game.turn,
    castling: {...game.castling},
    enPassant: game.enPassant
  };

  const captured = applyMove(board, game, move);
  if(captured){
    if(color==='w') game.capturedByWhite.push(captured);
    else game.capturedByBlack.push(captured);
  }

  game.turn = color === 'w' ? 'b' : 'w';

  const opponentInCheck = inCheck(board, game.turn);
  const opponentMoves = allLegalMoves(game.turn);
  let checkChar = '';
  let gameOver = false;
  let resultText = null;

  if(opponentMoves.length === 0){
    gameOver = true;
    if(opponentInCheck){
      checkChar = '#';
      resultText = (color==='w' ? 'White' : 'Black') + ' wins by checkmate';
    } else {
      resultText = 'Draw by stalemate';
    }
  } else if(opponentInCheck){
    checkChar = '+';
  }

  const notation = moveNotation(move, piece, wasCapture, checkChar);
  game.history.push({ notation, snapshot, color, captured, move });
  game.over = gameOver;
  game.result = resultText;
  if(gameOver){
    game.endReason = opponentInCheck ? 'checkmate' : 'stalemate';
    game.winner = opponentInCheck ? color : 'draw';
  }

  game.lastMove = { from: move.from, to: move.to };
  game.selected = null;
  game.legalMovesForSelected = [];

  render();
  updateMoveList();
  updateCaptures();
  updateStatus();

  if(gameOver && opponentInCheck) flashBanner('Checkmate', 'mate');
  else if(opponentInCheck) flashBanner('Check!', 'check');

  if(gameOver) scheduleGameOver();

  if(!gameOver && game.mode === 'computer' && game.turn === botColor()){
    botTimer = setTimeout(computerMove, 450);
  }

  if(game.mode === 'online' && online.roomCode){
    const payload = serializeRoomFromGame();
    if(gameOver) payload.status = 'finished';
    updateDoc(doc(db, 'rooms', online.roomCode), payload).catch(err => console.error('sync failed', err));
    if(gameOver) recordOnlineGameEnd(color, resultText);
  }
}

function undoOnce(){
  const last = game.history.pop();
  game.board = last.snapshot.board;
  game.turn = last.snapshot.turn;
  game.castling = last.snapshot.castling;
  game.enPassant = last.snapshot.enPassant;
  game.over = false;
  game.result = null;
  game.winner = null;
  game.endReason = null;
  game.overShown = false;
  game.selected = null;
  game.legalMovesForSelected = [];

  if(last.captured){
    const list = last.color === 'w' ? game.capturedByWhite : game.capturedByBlack;
    list.pop();
  }

  game.lastMove = game.history.length
    ? game.history[game.history.length - 1].move || null
    : null;
}

function undoMove(){
  if(game.mode === 'online') return;
  if(game.history.length === 0) return;
  clearTimeout(botTimer);
  clearTimeout(overTimer);
  undoOnce();
  // Against the computer, step back until it's the human's turn again.
  if(game.mode === 'computer' && game.turn !== game.humanColor && game.history.length > 0){
    undoOnce();
  }

  render();
  updateMoveList();
  updateCaptures();
  updateStatus();

  // If undoing left the computer to move (e.g. human is Black and it is White's first move), let it play.
  if(game.mode === 'computer' && game.turn === botColor()){
    botTimer = setTimeout(computerMove, 450);
  }
}

/* ---------------- Simple AI (minimax + alpha-beta, depth 3) ---------------- */

function evaluateBoard(board){
  let score = 0;
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(!p) continue;
    const val = PIECE_VALUE[p.type];
    score += p.color === 'w' ? val : -val;
  }
  return score; // positive favors white
}

function orderMoves(moves, board){
  return moves.slice().sort((a,b) => {
    const scoreOf = (m) => {
      let s = 0;
      const target = board[m.to.r][m.to.c];
      if(target) s += PIECE_VALUE[target.type];
      if(m.promotion) s += PIECE_VALUE[m.promotion];
      return s;
    };
    return scoreOf(b) - scoreOf(a);
  });
}

function minimax(board, state, depth, alpha, beta, maximizing){
  if(depth === 0){
    return evaluateBoard(board);
  }
  const color = maximizing ? 'w' : 'b';
  let moves = [];
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(p && p.color===color) moves.push(...generatePieceMoves(board, r, c, state));
  }
  // filter to legal
  const legal = [];
  for(const m of moves){
    const b2 = cloneBoard(board);
    const s2 = { castling: {...state.castling}, enPassant: state.enPassant };
    applyMove(b2, s2, m);
    if(!inCheck(b2, color)) legal.push(m);
  }
  if(legal.length === 0){
    if(inCheck(board, color)) return maximizing ? -100000 - depth : 100000 + depth;
    return 0;
  }
  const ordered = orderMoves(legal, board);

  if(maximizing){
    let best = -Infinity;
    for(const m of ordered){
      const b2 = cloneBoard(board);
      const s2 = { castling: {...state.castling}, enPassant: state.enPassant };
      applyMove(b2, s2, m);
      const val = minimax(b2, s2, depth-1, alpha, beta, false);
      best = Math.max(best, val);
      alpha = Math.max(alpha, val);
      if(beta <= alpha) break;
    }
    return best;
  } else {
    let best = Infinity;
    for(const m of ordered){
      const b2 = cloneBoard(board);
      const s2 = { castling: {...state.castling}, enPassant: state.enPassant };
      applyMove(b2, s2, m);
      const val = minimax(b2, s2, depth-1, alpha, beta, true);
      best = Math.min(best, val);
      beta = Math.min(beta, val);
      if(beta <= alpha) break;
    }
    return best;
  }
}

const DIFFICULTY_DEPTH = { easy: 1, medium: 2, hard: 3 };

function computerMove(){
  if(game.over || game.mode !== 'computer') return;
  const bot = botColor();
  if(game.turn !== bot) return;
  const moves = allLegalMoves(bot);
  if(moves.length === 0) return;

  // Easy mode: mostly random.
  if(game.difficulty === 'easy' && Math.random() < 0.7){
    playMove(moves[Math.floor(Math.random()*moves.length)]);
    return;
  }

  const botIsWhite = bot === 'w';
  const depth = DIFFICULTY_DEPTH[game.difficulty] || 2;
  const ordered = orderMoves(moves, game.board);
  let bestMoves = [];
  let bestScore = botIsWhite ? -Infinity : Infinity;
  for(const m of ordered){
    const b2 = cloneBoard(game.board);
    const s2 = { castling: {...game.castling}, enPassant: game.enPassant };
    applyMove(b2, s2, m);
    // After the bot moves, the opponent is to move: white maximizes, black minimizes.
    const score = minimax(b2, s2, depth, -Infinity, Infinity, !botIsWhite);
    const better = botIsWhite ? score > bestScore : score < bestScore;
    if(better){
      bestScore = score;
      bestMoves = [m];
    } else if(score === bestScore){
      bestMoves.push(m);
    }
  }
  playMove(bestMoves[Math.floor(Math.random()*bestMoves.length)]);
}

/* ---------------- Rendering ---------------- */

const boardEl = document.getElementById('board');
const statusEl = document.getElementById('status');
const moveListEl = document.getElementById('moveList');
const capturedByWhiteEl = document.getElementById('capturedByWhite');
const capturedByBlackEl = document.getElementById('capturedByBlack');
const promoModal = document.getElementById('promoModal');
const promoChoices = document.getElementById('promoChoices');

function displayCoords(){
  // Unflipped: rank 8 at the top, file a on the left (White at the bottom).
  const fwd = [0,1,2,3,4,5,6,7];
  const rev = [7,6,5,4,3,2,1,0];
  const rows = game.flipped ? rev : fwd;
  const cols = game.flipped ? rev : fwd;
  return { rows, cols };
}

/* Squares of enemy pieces currently giving check to `color`'s king. */
function findCheckers(board, color){
  const k = findKing(board, color);
  if(!k) return [];
  const enemy = color === 'w' ? 'b' : 'w';
  const out = [];
  for(let r=0;r<8;r++) for(let c=0;c<8;c++){
    const p = board[r][c];
    if(!p || p.color !== enemy) continue;
    const hits = generatePieceMoves(board, r, c, { castling: {wK:false,wQ:false,bK:false,bQ:false}, enPassant: null })
      .some(m => m.to.r === k.r && m.to.c === k.c);
    if(hits) out.push({ r, c });
  }
  return out;
}

function render(){
  boardEl.innerHTML = '';
  const { rows, cols } = displayCoords();
  const checkedColor = ['w','b'].find(col => inCheck(game.board, col)) || null;
  const checkers = checkedColor ? findCheckers(game.board, checkedColor) : [];

  for(const r of rows){
    for(const c of cols){
      const square = document.createElement('div');
      const isLight = (r+c) % 2 === 0;
      square.className = 'square ' + (isLight ? 'light' : 'dark');
      square.dataset.r = r;
      square.dataset.c = c;

      if(game.lastMove && ((game.lastMove.from.r===r && game.lastMove.from.c===c) || (game.lastMove.to.r===r && game.lastMove.to.c===c))){
        square.classList.add('last-move');
      }

      if(game.selected && game.selected.r===r && game.selected.c===c){
        square.classList.add('selected');
      }

      const piece = game.board[r][c];
      if(piece){
        const span = document.createElement('span');
        span.className = 'piece ' + (piece.color === 'w' ? 'piece-white' : 'piece-black');
        span.textContent = UNICODE[piece.color][piece.type];
        square.appendChild(span);

        if(piece.type === 'k' && piece.color === checkedColor){
          square.classList.add('king-check');
        }
      }

      if(checkers.some(ck => ck.r === r && ck.c === c)){
        square.classList.add('checker');
      }

      const isLegalTarget = game.legalMovesForSelected.find(m => m.to.r===r && m.to.c===c);
      if(isLegalTarget){
        const marker = document.createElement('div');
        marker.className = piece ? 'capture-ring' : 'move-dot';
        square.appendChild(marker);
      }

      square.addEventListener('click', onSquareClick);
      boardEl.appendChild(square);
    }
  }
}

function onSquareClick(e){
  if(game.over) return;
  if(game.mode === 'computer' && game.turn !== game.humanColor) return;
  if(game.mode === 'online' && (online.status !== 'active' || game.turn !== online.myColor)) return;

  const r = parseInt(e.currentTarget.dataset.r, 10);
  const c = parseInt(e.currentTarget.dataset.c, 10);
  const piece = game.board[r][c];

  if(game.selected){
    const move = game.legalMovesForSelected.find(m => m.to.r===r && m.to.c===c);
    if(move){
      if(move.promotion){
        askPromotion(move.to.r, move.to.c, (chosen) => {
          const promoMove = game.legalMovesForSelected.find(m => m.to.r===r && m.to.c===c && m.promotion===chosen);
          playMove(promoMove);
        });
        return;
      }
      playMove(move);
      return;
    }
    if(piece && piece.color === game.turn){
      game.selected = {r,c};
      game.legalMovesForSelected = legalMovesFrom(r,c);
      render();
      return;
    }
    game.selected = null;
    game.legalMovesForSelected = [];
    render();
    return;
  }

  if(piece && piece.color === game.turn){
    game.selected = {r,c};
    game.legalMovesForSelected = legalMovesFrom(r,c);
    render();
  }
}

function askPromotion(r, c, callback){
  const color = game.turn;
  promoChoices.innerHTML = '';
  for(const type of ['q','r','b','n']){
    const btn = document.createElement('button');
    btn.textContent = UNICODE[color][type];
    btn.addEventListener('click', () => {
      promoModal.classList.add('hidden');
      callback(type);
    });
    promoChoices.appendChild(btn);
  }
  promoModal.classList.remove('hidden');
}

/* ---------------- Status, check banner and game-over screen ---------------- */

const boardFrameEl = document.getElementById('boardFrame');
const boardSurfaceEl = document.getElementById('boardSurface');
const checkBannerEl = document.getElementById('checkBanner');
const gameInfoTitleEl = document.getElementById('gameInfoTitle');
const gameInfoTextEl = document.getElementById('gameInfoText');

function cap(str){ return str.charAt(0).toUpperCase() + str.slice(1); }

function updateStatus(){
  statusEl.classList.remove('check','win');
  const checkedNow = !game.over && inCheck(game.board, game.turn);
  const mated = game.over && game.endReason === 'checkmate';
  boardFrameEl.classList.toggle('in-check', checkedNow || mated);

  if(game.over){
    statusEl.textContent = game.result;
    statusEl.classList.add(mated ? 'check' : 'win');
  } else {
    const turnName = game.turn === 'w' ? 'White' : 'Black';
    if(checkedNow){
      statusEl.textContent = turnName + ' is in check!';
      statusEl.classList.add('check');
    } else {
      statusEl.textContent = turnName + ' to move';
    }
  }
  updateGameInfo();
}

function updateGameInfo(){
  if(!game) return;
  let title = '';
  let text = '';
  if(game.mode === 'computer'){
    const you = game.humanColor === 'w' ? 'White' : 'Black';
    title = 'Vs. computer · ' + cap(game.difficulty);
    if(game.over) text = (game.result || 'Game over') + '.';
    else text = game.turn === game.humanColor
      ? `You play ${you} — your move.`
      : `You play ${you} — the computer is thinking…`;
  } else if(game.mode === 'online'){
    title = 'Online' + (online.roomCode ? ' · Room ' + online.roomCode : '');
    const players = online.players || {};
    const oppColor = online.myColor === 'w' ? 'b' : 'w';
    const oppName = players[oppColor];
    if(game.over) text = (game.result || 'Game over') + '.';
    else if(!oppName) text = 'Waiting for an opponent…';
    else text = `Playing ${oppName} as ${online.myColor === 'w' ? 'White' : 'Black'} — ${game.turn === online.myColor ? 'your move' : "opponent's move"}.`;
  } else {
    title = 'Free board';
    text = game.over ? (game.result || 'Game over') + '.' : 'Move both sides. Undo and flip whenever you like.';
  }
  gameInfoTitleEl.textContent = title;
  gameInfoTextEl.textContent = text;
}

function flashBanner(text, kind){
  checkBannerEl.textContent = text;
  checkBannerEl.className = 'check-banner ' + kind;
  void checkBannerEl.offsetWidth; // restart the CSS animation
  checkBannerEl.classList.add('show');
  boardSurfaceEl.classList.remove('shake');
  void boardSurfaceEl.offsetWidth;
  boardSurfaceEl.classList.add('shake');
}

const gameOverModal = document.getElementById('gameOverModal');
const resultCardEl = document.getElementById('resultCard');
const resultKickerEl = document.getElementById('resultKicker');
const resultTitleEl = document.getElementById('resultTitle');
const resultWEl = document.getElementById('resultW');
const resultBEl = document.getElementById('resultB');
const resultMetaEl = document.getElementById('resultMeta');
const playAgainBtn = document.getElementById('playAgainBtn');

function scheduleGameOver(){
  if(game.overShown) return;
  game.overShown = true;
  clearTimeout(overTimer);
  const delay = game.endReason === 'checkmate' ? 1500 : game.endReason === 'resign' ? 300 : 900;
  overTimer = setTimeout(showGameOver, delay);
}

function playerNames(){
  if(game.mode === 'computer'){
    const bot = 'Computer (' + cap(game.difficulty) + ')';
    return game.humanColor === 'w' ? { w: myUsername + ' (you)', b: bot } : { w: bot, b: myUsername + ' (you)' };
  }
  if(game.mode === 'online'){
    const pl = online.players || {};
    const tag = (n, col) => (n || (col === 'w' ? 'White' : 'Black')) + (online.myColor === col ? ' (you)' : '');
    return { w: tag(pl.w, 'w'), b: tag(pl.b, 'b') };
  }
  return { w: 'White', b: 'Black' };
}

function showGameOver(){
  if(!game.over) return;
  const winner = game.winner;
  const perspective = game.mode === 'computer' ? game.humanColor : (game.mode === 'online' ? online.myColor : null);

  let outcome, title;
  if(winner === 'draw'){
    outcome = 'draw'; title = 'Draw';
  } else if(perspective){
    outcome = winner === perspective ? 'win' : 'loss';
    title = outcome === 'win' ? 'You won!' : 'You lost';
  } else {
    outcome = 'neutral';
    title = (winner === 'w' ? 'White' : 'Black') + ' wins';
  }

  const reasons = { checkmate: 'Checkmate', stalemate: 'Stalemate', resign: 'Resignation' };
  resultKickerEl.textContent = reasons[game.endReason] || 'Game over';
  resultTitleEl.textContent = title;
  resultCardEl.className = 'modal-card result-card ' + outcome;

  const names = playerNames();
  const fill = (el, color) => {
    el.querySelector('.rp-name').textContent = names[color];
    const tag = el.querySelector('.rp-tag');
    el.classList.remove('is-winner', 'is-loser', 'is-draw');
    if(winner === 'draw'){ tag.textContent = 'Draw'; el.classList.add('is-draw'); }
    else if(winner === color){ tag.textContent = 'Winner'; el.classList.add('is-winner'); }
    else { tag.textContent = game.endReason === 'resign' ? 'Resigned' : 'Defeated'; el.classList.add('is-loser'); }
  };
  fill(resultWEl, 'w');
  fill(resultBEl, 'b');

  const moves = Math.ceil(game.history.length / 2);
  let meta = `${moves} move${moves === 1 ? '' : 's'}`;
  if(game.mode === 'online') meta += ' · result recorded on the leaderboard';
  resultMetaEl.textContent = meta;

  playAgainBtn.classList.toggle('hidden', game.mode === 'online');
  gameOverModal.classList.remove('hidden');
}

function updateMoveList(){
  moveListEl.innerHTML = '';
  const moves = game.history.map(h => h.notation);
  for(let i=0; i<moves.length; i+=2){
    const li = document.createElement('li');
    const num = document.createElement('span');
    num.className = 'mv-num';
    num.textContent = (i/2 + 1) + '.';
    const white = document.createElement('span');
    white.className = 'mv-white';
    white.textContent = moves[i] || '';
    const black = document.createElement('span');
    black.className = 'mv-black';
    black.textContent = moves[i+1] || '';
    li.appendChild(num);
    li.appendChild(white);
    li.appendChild(black);
    moveListEl.appendChild(li);
  }
  moveListEl.scrollTop = moveListEl.scrollHeight;
}

function updateCaptures(){
  capturedByWhiteEl.textContent = game.capturedByWhite.map(p => UNICODE['b'][p.type]).join(' ');
  capturedByBlackEl.textContent = game.capturedByBlack.map(p => UNICODE['w'][p.type]).join(' ');
}

/* ---------------- Username system ---------------- */

const usernameBtn = document.getElementById('usernameBtn');
const usernameModal = document.getElementById('usernameModal');
const usernameInput = document.getElementById('usernameInput');
const usernameError = document.getElementById('usernameError');
const usernameSaveBtn = document.getElementById('usernameSaveBtn');

function playerDocId(name){
  return (name || '').trim().toLowerCase().replace(/[^a-z0-9_-]/g, '_').slice(0, 40) || 'guest';
}

function ensureUsername(){
  let name = localStorage.getItem('endgame_username');
  if(!name){
    name = 'Guest' + Math.floor(1000 + Math.random() * 9000);
    localStorage.setItem('endgame_username', name);
  }
  return name;
}

let myUsername = ensureUsername();

async function upsertPlayerDoc(name){
  try{
    const ref = doc(db, 'players', playerDocId(name));
    const snap = await getDoc(ref);
    if(!snap.exists()){
      await setDoc(ref, { username: name, wins: 0, losses: 0, draws: 0, updatedAt: serverTimestamp() });
    } else {
      await updateDoc(ref, { username: name, updatedAt: serverTimestamp() });
    }
  }catch(err){
    console.error('Could not save player profile', err);
  }
}

function openUsernameModal(){
  usernameInput.value = myUsername;
  usernameError.classList.add('hidden');
  usernameModal.classList.remove('hidden');
  usernameInput.focus();
  usernameInput.select();
}

usernameBtn.addEventListener('click', openUsernameModal);

usernameSaveBtn.addEventListener('click', () => {
  const name = usernameInput.value.trim().slice(0, 18);
  if(name.length < 2){
    usernameError.textContent = 'Please enter at least 2 characters.';
    usernameError.classList.remove('hidden');
    return;
  }
  myUsername = name;
  localStorage.setItem('endgame_username', name);
  usernameBtn.textContent = name;
  usernameModal.classList.add('hidden');
  upsertPlayerDoc(name);
});

usernameInput.addEventListener('keydown', (e) => {
  if(e.key === 'Enter') usernameSaveBtn.click();
});

usernameBtn.textContent = myUsername;
upsertPlayerDoc(myUsername);

/* ---------------- Live leaderboard ---------------- */

const leaderboardListEls = [
  document.getElementById('leaderboardList'),
  document.getElementById('leaderboardListGame')
];

function renderLeaderboard(rows){
  for(const listEl of leaderboardListEls){
    listEl.innerHTML = '';
    if(rows.length === 0){
      listEl.innerHTML = '<li class="leaderboard-empty">No games recorded yet — play one online!</li>';
      continue;
    }
    rows.forEach((r, i) => {
      const li = document.createElement('li');
      if(r.username === myUsername) li.className = 'is-me';
      const rank = document.createElement('span');
      rank.className = 'lb-rank';
      rank.textContent = (i + 1) + '.';
      const name = document.createElement('span');
      name.className = 'lb-name';
      name.textContent = r.username || 'Guest';
      const rec = document.createElement('span');
      rec.className = 'lb-record';
      rec.textContent = `${r.wins || 0}W ${r.losses || 0}L ${r.draws || 0}D`;
      li.appendChild(rank);
      li.appendChild(name);
      li.appendChild(rec);
      listEl.appendChild(li);
    });
  }
}

function subscribeLeaderboard(){
  try{
    const q = query(collection(db, 'players'), orderBy('wins', 'desc'), limit(20));
    onSnapshot(q, (snap) => {
      const rows = [];
      snap.forEach(d => rows.push(d.data()));
      renderLeaderboard(rows);
    }, (err) => {
      console.error('Leaderboard listener error', err);
      leaderboardListEls.forEach(el => { el.innerHTML = '<li class="leaderboard-empty">Leaderboard unavailable right now.</li>'; });
    });
  }catch(err){
    console.error(err);
  }
}

async function recordResult(winnerName, loserName){
  try{
    await setDoc(doc(db, 'players', playerDocId(winnerName)),
      { username: winnerName, wins: increment(1), losses: increment(0), draws: increment(0), updatedAt: serverTimestamp() },
      { merge: true });
    await setDoc(doc(db, 'players', playerDocId(loserName)),
      { username: loserName, wins: increment(0), losses: increment(1), draws: increment(0), updatedAt: serverTimestamp() },
      { merge: true });
  }catch(err){
    console.error('Could not record result', err);
  }
}

async function recordDraw(nameA, nameB){
  try{
    for(const n of [nameA, nameB]){
      await setDoc(doc(db, 'players', playerDocId(n)),
        { username: n, wins: increment(0), losses: increment(0), draws: increment(1), updatedAt: serverTimestamp() },
        { merge: true });
    }
  }catch(err){
    console.error('Could not record draw', err);
  }
}

/* ---------------- Online multiplayer rooms ---------------- */

const ROOM_CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'; // no 0/O or 1/I
function generateRoomCode(){
  let s = '';
  for(let i=0;i<5;i++) s += ROOM_CODE_CHARS[Math.floor(Math.random() * ROOM_CODE_CHARS.length)];
  return s;
}

const online = {
  roomCode: null,
  myColor: null,
  status: 'idle', // idle | waiting | active | finished | abandoned
  players: null,
  unsub: null
};

const onlineLobbyEl = document.getElementById('onlineLobby');
const onlineActiveEl = document.getElementById('onlineActive');
const onlineErrorEl = document.getElementById('onlineError');
const roomCodeDisplayEl = document.getElementById('roomCodeDisplay');
const joinRoomInput = document.getElementById('joinRoomInput');
const createRoomBtn = document.getElementById('createRoomBtn');
const joinRoomBtn = document.getElementById('joinRoomBtn');
const leaveRoomBtn = document.getElementById('leaveRoomBtn');

function showOnlineError(msg){
  onlineErrorEl.textContent = msg;
  onlineErrorEl.classList.remove('hidden');
}

function resetOnlineUI(){
  online.roomCode = null;
  online.myColor = null;
  online.status = 'idle';
  online.players = null;
  if(online.unsub){ online.unsub(); online.unsub = null; }
  onlineLobbyEl.classList.remove('hidden');
  onlineActiveEl.classList.add('hidden');
  onlineErrorEl.classList.add('hidden');
  joinRoomInput.value = '';
}

function serializeRoomFromGame(){
  return {
    boardJSON: JSON.stringify(game.board),
    turn: game.turn,
    castling: { ...game.castling },
    enPassant: game.enPassant || null,
    capturedByWhite: game.capturedByWhite,
    capturedByBlack: game.capturedByBlack,
    historyNotation: game.history.map(h => h.notation),
    over: game.over,
    result: game.result,
    winner: game.winner || null,
    endReason: game.endReason || null,
    lastMove: game.lastMove || null
  };
}

function loadRemoteState(data){
  if(!data.boardJSON) return;
  const prevLen = game.history.length;
  game.board = JSON.parse(data.boardJSON);
  game.turn = data.turn;
  game.castling = data.castling;
  game.enPassant = data.enPassant || null;
  game.capturedByWhite = data.capturedByWhite || [];
  game.capturedByBlack = data.capturedByBlack || [];
  game.over = !!data.over;
  game.result = data.result || null;
  game.winner = data.winner || null;
  game.endReason = data.endReason || null;
  game.lastMove = data.lastMove || null;
  game.history = (data.historyNotation || []).map(n => ({ notation: n }));
  game.selected = null;
  game.legalMovesForSelected = [];
  render();
  updateMoveList();
  updateCaptures();
  updateStatus();

  // Only announce check / mate for moves that arrived from the opponent.
  const newMove = game.history.length > prevLen;
  if(newMove && game.over && game.endReason === 'checkmate') flashBanner('Checkmate', 'mate');
  else if(newMove && !game.over && inCheck(game.board, game.turn)) flashBanner('Check!', 'check');
  if(game.over && game.winner) scheduleGameOver();
}

function updateOnlineStatusText(){ updateGameInfo(); }

function recordOnlineGameEnd(moverColor, resultText){
  const players = online.players;
  if(!players || !players.w || !players.b) return;
  if(resultText && /checkmate/i.test(resultText)){
    const winnerName = moverColor === 'w' ? players.w : players.b;
    const loserName = moverColor === 'w' ? players.b : players.w;
    recordResult(winnerName, loserName);
  } else if(resultText && /(stalemate|draw)/i.test(resultText)){
    recordDraw(players.w, players.b);
  }
}

function subscribeRoom(code){
  const ref = doc(db, 'rooms', code);
  online.unsub = onSnapshot(ref, (snap) => {
    if(!snap.exists()) return;
    const data = snap.data();
    online.players = data.players || online.players;
    online.status = data.status || online.status;
    loadRemoteState(data);
    updateOnlineStatusText();
    // Host: the moment an opponent joins, leave the lobby and start playing.
    if(currentView === 'lobby' && online.status === 'active' && online.myColor) enterOnlineGame();
  }, (err) => {
    console.error('Room listener error', err);
    showOnlineError('Lost connection to the room.');
  });
}

function startFreshOnlineGame(){
  newGame({ mode: 'online' });
}

function enterOnlineGame(){
  game.flipped = online.myColor === 'b';
  showGame();
}

async function createRoom(){
  onlineErrorEl.classList.add('hidden');
  createRoomBtn.disabled = true;
  const code = generateRoomCode();
  startFreshOnlineGame();
  online.roomCode = code;
  online.myColor = 'w';
  online.status = 'waiting';
  online.players = { w: myUsername, b: null };
  const initial = serializeRoomFromGame();
  initial.players = { w: myUsername, b: null };
  initial.status = 'waiting';
  try{
    await setDoc(doc(db, 'rooms', code), initial);
    subscribeRoom(code);
    onlineLobbyEl.classList.add('hidden');
    onlineActiveEl.classList.remove('hidden');
    roomCodeDisplayEl.textContent = code;
    updateOnlineStatusText();
  }catch(err){
    console.error(err);
    showOnlineError('Could not create a room — check your connection and Firestore setup.');
    online.status = 'idle';
  }finally{
    createRoomBtn.disabled = false;
  }
}

async function joinRoom(){
  const code = joinRoomInput.value.trim().toUpperCase();
  onlineErrorEl.classList.add('hidden');
  if(code.length !== 5){
    showOnlineError('Enter the 5-character room code.');
    return;
  }
  joinRoomBtn.disabled = true;
  try{
    const ref = doc(db, 'rooms', code);
    const snap = await getDoc(ref);
    if(!snap.exists()){
      showOnlineError('No room found with that code.');
      return;
    }
    const data = snap.data();
    if(data.status !== 'waiting'){
      showOnlineError('That room is not open for joining.');
      return;
    }
    await updateDoc(ref, { 'players.b': myUsername, status: 'active' });
    startFreshOnlineGame();
    online.roomCode = code;
    online.myColor = 'b';
    online.status = 'active';
    online.players = { w: data.players.w, b: myUsername };
    subscribeRoom(code);
    onlineLobbyEl.classList.add('hidden');
    onlineActiveEl.classList.remove('hidden');
    roomCodeDisplayEl.textContent = code;
    enterOnlineGame();
  }catch(err){
    console.error(err);
    showOnlineError('Could not join that room — check your connection and Firestore setup.');
  }finally{
    joinRoomBtn.disabled = false;
  }
}

async function leaveOrResign(){
  if(online.status === 'active' && !game.over){
    const players = online.players || {};
    const oppColor = online.myColor === 'w' ? 'b' : 'w';
    const oppName = players[oppColor];
    const myName = players[online.myColor];
    game.over = true;
    game.overShown = true; // we're leaving; don't pop the result screen for ourselves
    game.winner = oppColor;
    game.endReason = 'resign';
    game.result = (oppColor === 'w' ? 'White' : 'Black') + ' wins — opponent resigned';
    try{
      const payload = serializeRoomFromGame();
      payload.status = 'finished';
      await updateDoc(doc(db, 'rooms', online.roomCode), payload);
    }catch(err){ console.error(err); }
    if(oppName && myName) recordResult(oppName, myName);
  } else if(online.roomCode && online.status === 'waiting'){
    try{ await updateDoc(doc(db, 'rooms', online.roomCode), { status: 'abandoned' }); }catch(err){ /* ignore */ }
  }
  resetOnlineUI();
  render();
  updateStatus();
}

createRoomBtn.addEventListener('click', () => { if(online.status === 'idle') createRoom(); });
joinRoomBtn.addEventListener('click', () => { if(online.status === 'idle') joinRoom(); });
leaveRoomBtn.addEventListener('click', leaveOrResign);
joinRoomInput.addEventListener('input', () => { joinRoomInput.value = joinRoomInput.value.toUpperCase(); });
joinRoomInput.addEventListener('keydown', (e) => { if(e.key === 'Enter') joinRoomBtn.click(); });

/* ---------------- Views: lobby and game ---------------- */

const lobbyViewEl = document.getElementById('lobbyView');
const gameViewEl = document.getElementById('gameView');
const newGameBtn = document.getElementById('newGameBtn');
const undoBtn = document.getElementById('undoBtn');
let currentView = 'lobby';

function showGame(){
  lobbyViewEl.classList.add('hidden');
  gameViewEl.classList.remove('hidden');
  currentView = 'game';
  const isOnline = game.mode === 'online';
  newGameBtn.classList.toggle('hidden', isOnline);
  undoBtn.classList.toggle('hidden', isOnline);
  checkBannerEl.className = 'check-banner';
  render();
  updateMoveList();
  updateCaptures();
  updateStatus();
}

function showLobby(){
  clearTimeout(botTimer);
  clearTimeout(overTimer);
  gameOverModal.classList.add('hidden');
  promoModal.classList.add('hidden');
  gameViewEl.classList.add('hidden');
  lobbyViewEl.classList.remove('hidden');
  currentView = 'lobby';
}

let lastBotSetup = { difficulty: 'medium', colorChoice: 'w' };

function startBotGame(difficulty, colorChoice){
  lastBotSetup = { difficulty, colorChoice };
  const humanColor = colorChoice === 'random' ? (Math.random() < 0.5 ? 'w' : 'b') : colorChoice;
  newGame({ mode: 'computer', difficulty, humanColor });
  showGame();
  if(botColor() === 'w') botTimer = setTimeout(computerMove, 700);
}

function startFreeGame(){
  newGame({ mode: 'two-player' });
  showGame();
}

function restartCurrentGame(){
  gameOverModal.classList.add('hidden');
  if(game.mode === 'computer') startBotGame(lastBotSetup.difficulty, lastBotSetup.colorChoice);
  else if(game.mode === 'two-player') startFreeGame();
}

async function leaveToLobby(){
  if(game.mode === 'online'){
    if(online.status === 'active' && !game.over){
      if(!confirm('Leave this game? Leaving counts as a resignation.')) return;
    }
    await leaveOrResign();
  }
  showLobby();
}

/* ---------------- Lobby controls ---------------- */

let lobbyDifficulty = 'medium';
let lobbyColor = 'w';

function wireSegment(id, onChange){
  const el = document.getElementById(id);
  el.addEventListener('click', (e) => {
    const btn = e.target.closest('.mode-option');
    if(!btn) return;
    el.querySelectorAll('.mode-option').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    onChange(btn.dataset.value);
  });
}

wireSegment('botDifficulty', v => { lobbyDifficulty = v; });
wireSegment('botColor', v => { lobbyColor = v; });

document.getElementById('startBotBtn').addEventListener('click', () => startBotGame(lobbyDifficulty, lobbyColor));
document.getElementById('startFreeBtn').addEventListener('click', startFreeGame);

/* ---------------- In-game controls ---------------- */

newGameBtn.addEventListener('click', () => {
  if(game.mode === 'online') return;
  restartCurrentGame();
});

undoBtn.addEventListener('click', undoMove);

document.getElementById('flipBtn').addEventListener('click', () => {
  game.flipped = !game.flipped;
  render();
});

document.getElementById('backToLobbyBtn').addEventListener('click', leaveToLobby);

/* ---------------- Game-over screen buttons ---------------- */

playAgainBtn.addEventListener('click', restartCurrentGame);
document.getElementById('viewBoardBtn').addEventListener('click', () => gameOverModal.classList.add('hidden'));
document.getElementById('resultLobbyBtn').addEventListener('click', () => {
  gameOverModal.classList.add('hidden');
  leaveToLobby();
});

/* ---------------- Boot ---------------- */

newGame();
subscribeLeaderboard();
