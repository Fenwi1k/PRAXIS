/**
 * Ray-based bitboard chess board for an engine.
 *
 * Square mapping (little-endian rank-file): a1 = 0, b1 = 1, ... h1 = 7, a2 = 8, ... h8 = 63.
 *
 * Sliding attacks use the "classical" ray approach:
 *   1. Precompute RAYS[direction][square] = every square on that ray out to the board edge.
 *   2. For a ray, find the first blocker with a bitscan, then XOR away the ray that starts
 *      at the blocker. What is left is the attack set, including the blocker square itself.
 *   Positive directions (N, NE, E, NW) have the first blocker at the lowest set bit.
 *   Negative directions (SE, S, SW, W) have the first blocker at the highest set bit.
 *
 * Run directly (Java 11+):   java Board.java
 */
public final class Board {

    // ---------- Constants ----------
    public static final int WHITE = 0, BLACK = 1;
    public static final int PAWN = 0, KNIGHT = 1, BISHOP = 2, ROOK = 3, QUEEN = 4, KING = 5;
    public static final int NONE = 12;                    // "no piece" in the mailbox

    // Piece code = color * 6 + type  (0..5 white, 6..11 black)
    private static final String PIECE_CHARS = "PNBRQKpnbrqk";

    // Castling rights bits
    public static final int WK = 1, WQ = 2, BK = 4, BQ = 8;

    // Move flags
    public static final int FLAG_QUIET = 0, FLAG_DOUBLE = 1, FLAG_EP = 2,
                            FLAG_CASTLE_K = 3, FLAG_CASTLE_Q = 4;

    // Ray directions
    private static final int N = 0, NE = 1, E = 2, SE = 3, S = 4, SW = 5, W = 6, NW = 7;
    private static final int[] DR = { 1, 1, 0, -1, -1, -1, 0, 1 };
    private static final int[] DF = { 0, 1, 1, 1, 0, -1, -1, -1 };
    private static final boolean[] POSITIVE = new boolean[8];

    // ---------- Precomputed tables ----------
    private static final long[][] RAYS = new long[8][64];
    private static final long[] KNIGHT_ATTACKS = new long[64];
    private static final long[] KING_ATTACKS = new long[64];
    private static final long[][] PAWN_ATTACKS = new long[2][64];   // [color of the pawn][square]
    private static final int[] CASTLE_MASK = new int[64];

    static {
        for (int d = 0; d < 8; d++) POSITIVE[d] = DR[d] * 8 + DF[d] > 0;

        int[] knightDr = { 2, 2, 1, 1, -1, -1, -2, -2 };
        int[] knightDf = { 1, -1, 2, -2, 2, -2, 1, -1 };

        for (int sq = 0; sq < 64; sq++) {
            int r = sq >> 3, f = sq & 7;

            // Rays and king attacks
            for (int d = 0; d < 8; d++) {
                long ray = 0L;
                int rr = r + DR[d], ff = f + DF[d];
                boolean first = true;
                while (inBounds(rr, ff)) {
                    ray |= 1L << (rr * 8 + ff);
                    if (first) KING_ATTACKS[sq] |= 1L << (rr * 8 + ff);
                    first = false;
                    rr += DR[d];
                    ff += DF[d];
                }
                RAYS[d][sq] = ray;
            }

            // Knight attacks
            for (int i = 0; i < 8; i++) {
                int rr = r + knightDr[i], ff = f + knightDf[i];
                if (inBounds(rr, ff)) KNIGHT_ATTACKS[sq] |= 1L << (rr * 8 + ff);
            }

            // Pawn attacks
            for (int df : new int[] { -1, 1 }) {
                if (inBounds(r + 1, f + df)) PAWN_ATTACKS[WHITE][sq] |= 1L << ((r + 1) * 8 + f + df);
                if (inBounds(r - 1, f + df)) PAWN_ATTACKS[BLACK][sq] |= 1L << ((r - 1) * 8 + f + df);
            }

            CASTLE_MASK[sq] = 15;
        }

        CASTLE_MASK[0]  &= ~WQ;          // a1
        CASTLE_MASK[4]  &= ~(WK | WQ);   // e1
        CASTLE_MASK[7]  &= ~WK;          // h1
        CASTLE_MASK[56] &= ~BQ;          // a8
        CASTLE_MASK[60] &= ~(BK | BQ);   // e8
        CASTLE_MASK[63] &= ~BK;          // h8
    }

    private static boolean inBounds(int r, int f) {
        return r >= 0 && r < 8 && f >= 0 && f < 8;
    }

    // ---------- Position state ----------
    private final long[][] pieces = new long[2][6];   // [color][type]
    private final long[] occ = new long[2];           // occupancy per color
    private long all;                                 // total occupancy
    private final int[] mailbox = new int[64];        // piece code on each square, or NONE

    private int stm = WHITE;
    private int castling = 0;
    private int ep = -1;
    private int halfmove = 0;
    private int fullmove = 1;

    // Undo history
    private static final int MAX_PLY = 1024;
    private final int[] hMove = new int[MAX_PLY];
    private final int[] hCaptured = new int[MAX_PLY];
    private final int[] hCastle = new int[MAX_PLY];
    private final int[] hEp = new int[MAX_PLY];
    private final int[] hHalf = new int[MAX_PLY];
    private int ply = 0;

    public Board() {
        setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    }

    // ---------- Move encoding ----------
    // bits 0-5 from | 6-11 to | 12-14 promotion piece type (0 = none) | 15-17 flag
    public static int move(int from, int to, int promo, int flag) {
        return from | (to << 6) | (promo << 12) | (flag << 15);
    }
    public static int from(int m)  { return m & 63; }
    public static int to(int m)    { return (m >> 6) & 63; }
    public static int promo(int m) { return (m >> 12) & 7; }
    public static int flag(int m)  { return (m >> 15) & 7; }

    public static String squareName(int sq) {
        return "" + (char) ('a' + (sq & 7)) + (char) ('1' + (sq >> 3));
    }

    public static String moveToString(int m) {
        String s = squareName(from(m)) + squareName(to(m));
        if (promo(m) != 0) s += "?nbrq".charAt(promo(m));
        return s;
    }

    // ---------- Piece placement helpers ----------
    private void putPiece(int piece, int sq) {
        long bit = 1L << sq;
        int color = piece / 6, type = piece % 6;
        pieces[color][type] |= bit;
        occ[color] |= bit;
        all |= bit;
        mailbox[sq] = piece;
    }

    private void removePiece(int sq) {
        int piece = mailbox[sq];
        long bit = 1L << sq;
        int color = piece / 6, type = piece % 6;
        pieces[color][type] &= ~bit;
        occ[color] &= ~bit;
        all &= ~bit;
        mailbox[sq] = NONE;
    }

    private void movePiece(int from, int to) {
        int piece = mailbox[from];
        removePiece(from);
        putPiece(piece, to);
    }

    // ---------- Ray-based attack generation ----------
    private static long rayAttacks(int dir, int sq, long occupied) {
        long attacks = RAYS[dir][sq];
        long blockers = attacks & occupied;
        if (blockers != 0) {
            int first = POSITIVE[dir]
                    ? Long.numberOfTrailingZeros(blockers)
                    : 63 - Long.numberOfLeadingZeros(blockers);
            attacks ^= RAYS[dir][first];
        }
        return attacks;
    }

    public static long bishopAttacks(int sq, long occupied) {
        return rayAttacks(NE, sq, occupied) | rayAttacks(SE, sq, occupied)
             | rayAttacks(SW, sq, occupied) | rayAttacks(NW, sq, occupied);
    }

    public static long rookAttacks(int sq, long occupied) {
        return rayAttacks(N, sq, occupied) | rayAttacks(E, sq, occupied)
             | rayAttacks(S, sq, occupied) | rayAttacks(W, sq, occupied);
    }

    public static long queenAttacks(int sq, long occupied) {
        return bishopAttacks(sq, occupied) | rookAttacks(sq, occupied);
    }

    private static long attacksFrom(int type, int sq, long occupied) {
        switch (type) {
            case KNIGHT: return KNIGHT_ATTACKS[sq];
            case BISHOP: return bishopAttacks(sq, occupied);
            case ROOK:   return rookAttacks(sq, occupied);
            case QUEEN:  return queenAttacks(sq, occupied);
            case KING:   return KING_ATTACKS[sq];
            default:     return 0L;
        }
    }

    /** Is square sq attacked by any piece of color 'by'? */
    public boolean isAttacked(int sq, int by) {
        if ((PAWN_ATTACKS[by ^ 1][sq] & pieces[by][PAWN]) != 0) return true;
        if ((KNIGHT_ATTACKS[sq] & pieces[by][KNIGHT]) != 0) return true;
        if ((KING_ATTACKS[sq] & pieces[by][KING]) != 0) return true;
        if ((bishopAttacks(sq, all) & (pieces[by][BISHOP] | pieces[by][QUEEN])) != 0) return true;
        if ((rookAttacks(sq, all) & (pieces[by][ROOK] | pieces[by][QUEEN])) != 0) return true;
        return false;
    }

    public boolean inCheck() {
        long k = pieces[stm][KING];
        return k != 0 && isAttacked(Long.numberOfTrailingZeros(k), stm ^ 1);
    }

    // ---------- Move generation (pseudo-legal; legality is checked in makeMove) ----------
    public int generateMoves(int[] mv) {
        int n = 0;
        final int us = stm, them = us ^ 1;

        // Pawns
        long pawns = pieces[us][PAWN];
        final int dir = us == WHITE ? 8 : -8;
        final int startRank = us == WHITE ? 1 : 6;
        final int promoRank = us == WHITE ? 6 : 1;    // rank the pawn is on before it promotes
        while (pawns != 0) {
            int sq = Long.numberOfTrailingZeros(pawns);
            pawns &= pawns - 1;
            int rank = sq >> 3;
            int fwd = sq + dir;

            if (mailbox[fwd] == NONE) {
                if (rank == promoRank) {
                    n = addPromotions(mv, n, sq, fwd);
                } else {
                    mv[n++] = move(sq, fwd, 0, FLAG_QUIET);
                    if (rank == startRank && mailbox[fwd + dir] == NONE) {
                        mv[n++] = move(sq, fwd + dir, 0, FLAG_DOUBLE);
                    }
                }
            }

            long caps = PAWN_ATTACKS[us][sq] & occ[them];
            while (caps != 0) {
                int to = Long.numberOfTrailingZeros(caps);
                caps &= caps - 1;
                if (rank == promoRank) n = addPromotions(mv, n, sq, to);
                else mv[n++] = move(sq, to, 0, FLAG_QUIET);
            }

            if (ep != -1 && (PAWN_ATTACKS[us][sq] & (1L << ep)) != 0) {
                mv[n++] = move(sq, ep, 0, FLAG_EP);
            }
        }

        // Knights, bishops, rooks, queens, king
        for (int type = KNIGHT; type <= KING; type++) {
            long bb = pieces[us][type];
            while (bb != 0) {
                int from = Long.numberOfTrailingZeros(bb);
                bb &= bb - 1;
                long targets = attacksFrom(type, from, all) & ~occ[us];
                while (targets != 0) {
                    int to = Long.numberOfTrailingZeros(targets);
                    targets &= targets - 1;
                    mv[n++] = move(from, to, 0, FLAG_QUIET);
                }
            }
        }

        // Castling (standard chess)
        if (us == WHITE) {
            if ((castling & WK) != 0 && mailbox[5] == NONE && mailbox[6] == NONE
                    && !isAttacked(4, them) && !isAttacked(5, them) && !isAttacked(6, them)) {
                mv[n++] = move(4, 6, 0, FLAG_CASTLE_K);
            }
            if ((castling & WQ) != 0 && mailbox[1] == NONE && mailbox[2] == NONE && mailbox[3] == NONE
                    && !isAttacked(4, them) && !isAttacked(3, them) && !isAttacked(2, them)) {
                mv[n++] = move(4, 2, 0, FLAG_CASTLE_Q);
            }
        } else {
            if ((castling & BK) != 0 && mailbox[61] == NONE && mailbox[62] == NONE
                    && !isAttacked(60, them) && !isAttacked(61, them) && !isAttacked(62, them)) {
                mv[n++] = move(60, 62, 0, FLAG_CASTLE_K);
            }
            if ((castling & BQ) != 0 && mailbox[57] == NONE && mailbox[58] == NONE && mailbox[59] == NONE
                    && !isAttacked(60, them) && !isAttacked(59, them) && !isAttacked(58, them)) {
                mv[n++] = move(60, 58, 0, FLAG_CASTLE_Q);
            }
        }
        return n;
    }

    private static int addPromotions(int[] mv, int n, int from, int to) {
        mv[n++] = move(from, to, QUEEN, FLAG_QUIET);
        mv[n++] = move(from, to, ROOK, FLAG_QUIET);
        mv[n++] = move(from, to, BISHOP, FLAG_QUIET);
        mv[n++] = move(from, to, KNIGHT, FLAG_QUIET);
        return n;
    }

    // ---------- Legal move generation ----------
    /**
     * Fills 'out' with strictly legal moves for the side to move and returns how many.
     * Pseudo-legal moves are filtered by playing each one and rejecting those that leave
     * our own king attacked. 'out' must have room for at least 256 moves.
     */
    public int generateLegalMoves(int[] out) {
        int[] pseudo = new int[256];
        int n = generateMoves(pseudo);
        int count = 0;
        for (int i = 0; i < n; i++) {
            if (makeMove(pseudo[i])) {      // makeMove already undoes illegal moves itself
                unmakeMove();
                out[count++] = pseudo[i];
            }
        }
        return count;
    }

    /** True if the side to move has at least one legal move (stops at the first one found). */
    public boolean hasLegalMove() {
        int[] pseudo = new int[256];
        int n = generateMoves(pseudo);
        for (int i = 0; i < n; i++) {
            if (makeMove(pseudo[i])) {
                unmakeMove();
                return true;
            }
        }
        return false;
    }

    /** Is the given move (from/to/promo as encoded) legal here? Useful for validating GUI/UCI input. */
    public boolean isLegal(int m) {
        int[] legal = new int[256];
        int n = generateLegalMoves(legal);
        for (int i = 0; i < n; i++) if (legal[i] == m) return true;
        return false;
    }

    /** Parses a move in coordinate notation ("e2e4", "e7e8q") against the legal moves. Returns 0 if none match. */
    public int parseMove(String s) {
        int[] legal = new int[256];
        int n = generateLegalMoves(legal);
        for (int i = 0; i < n; i++) {
            if (moveToString(legal[i]).equals(s.trim().toLowerCase())) return legal[i];
        }
        return 0;
    }

    public boolean isCheckmate() { return inCheck() && !hasLegalMove(); }
    public boolean isStalemate() { return !inCheck() && !hasLegalMove(); }

    // ---------- Make / unmake ----------
    /** Plays the move. Returns false (and restores the position) if it leaves our king in check. */
    public boolean makeMove(int m) {
        final int from = from(m), to = to(m), promo = promo(m), flag = flag(m);
        final int us = stm, them = us ^ 1;
        final int piece = mailbox[from];
        int captured = mailbox[to];

        hMove[ply] = m;
        hCastle[ply] = castling;
        hEp[ply] = ep;
        hHalf[ply] = halfmove;

        if (flag == FLAG_EP) {
            int capSq = to + (us == WHITE ? -8 : 8);
            captured = mailbox[capSq];
            removePiece(capSq);
        } else if (captured != NONE) {
            removePiece(to);
        }
        hCaptured[ply] = captured;

        removePiece(from);
        putPiece(promo != 0 ? us * 6 + promo : piece, to);

        if (flag == FLAG_CASTLE_K) movePiece(to + 1, to - 1);
        else if (flag == FLAG_CASTLE_Q) movePiece(to - 2, to + 1);

        ep = flag == FLAG_DOUBLE ? (from + to) / 2 : -1;
        castling &= CASTLE_MASK[from] & CASTLE_MASK[to];
        halfmove = (piece % 6 == PAWN || captured != NONE) ? 0 : halfmove + 1;
        if (us == BLACK) fullmove++;
        stm = them;
        ply++;

        long k = pieces[us][KING];
        if (k != 0 && isAttacked(Long.numberOfTrailingZeros(k), them)) {
            unmakeMove();
            return false;
        }
        return true;
    }

    public void unmakeMove() {
        ply--;
        final int m = hMove[ply];
        final int from = from(m), to = to(m), promo = promo(m), flag = flag(m);
        stm ^= 1;
        final int us = stm;
        if (us == BLACK) fullmove--;

        if (flag == FLAG_CASTLE_K) movePiece(to - 1, to + 1);
        else if (flag == FLAG_CASTLE_Q) movePiece(to + 1, to - 2);

        int movedPiece = promo != 0 ? us * 6 + PAWN : mailbox[to];
        removePiece(to);
        putPiece(movedPiece, from);

        int captured = hCaptured[ply];
        if (captured != NONE) {
            int capSq = flag == FLAG_EP ? to + (us == WHITE ? -8 : 8) : to;
            putPiece(captured, capSq);
        }

        castling = hCastle[ply];
        ep = hEp[ply];
        halfmove = hHalf[ply];
    }

    // ---------- FEN ----------
    public void setFen(String fen) {
        for (int c = 0; c < 2; c++) {
            occ[c] = 0L;
            for (int t = 0; t < 6; t++) pieces[c][t] = 0L;
        }
        all = 0L;
        java.util.Arrays.fill(mailbox, NONE);
        ply = 0;

        String[] p = fen.trim().split("\\s+");
        int rank = 7, file = 0;
        for (char c : p[0].toCharArray()) {
            if (c == '/') { rank--; file = 0; }
            else if (Character.isDigit(c)) file += c - '0';
            else {
                putPiece(PIECE_CHARS.indexOf(c), rank * 8 + file);
                file++;
            }
        }

        stm = p.length > 1 && p[1].equals("b") ? BLACK : WHITE;

        castling = 0;
        if (p.length > 2) {
            for (char c : p[2].toCharArray()) {
                if (c == 'K') castling |= WK;
                else if (c == 'Q') castling |= WQ;
                else if (c == 'k') castling |= BK;
                else if (c == 'q') castling |= BQ;
            }
        }

        ep = -1;
        if (p.length > 3 && !p[3].equals("-")) {
            ep = (p[3].charAt(0) - 'a') + 8 * (p[3].charAt(1) - '1');
        }
        halfmove = p.length > 4 ? Integer.parseInt(p[4]) : 0;
        fullmove = p.length > 5 ? Integer.parseInt(p[5]) : 1;
    }

    public String toFen() {
        StringBuilder sb = new StringBuilder();
        for (int r = 7; r >= 0; r--) {
            int empty = 0;
            for (int f = 0; f < 8; f++) {
                int pc = mailbox[r * 8 + f];
                if (pc == NONE) { empty++; continue; }
                if (empty > 0) { sb.append(empty); empty = 0; }
                sb.append(PIECE_CHARS.charAt(pc));
            }
            if (empty > 0) sb.append(empty);
            if (r > 0) sb.append('/');
        }
        sb.append(stm == WHITE ? " w " : " b ");
        if (castling == 0) sb.append('-');
        else {
            if ((castling & WK) != 0) sb.append('K');
            if ((castling & WQ) != 0) sb.append('Q');
            if ((castling & BK) != 0) sb.append('k');
            if ((castling & BQ) != 0) sb.append('q');
        }
        sb.append(' ').append(ep == -1 ? "-" : squareName(ep));
        sb.append(' ').append(halfmove).append(' ').append(fullmove);
        return sb.toString();
    }

    // ---------- Debug printing ----------
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (int r = 7; r >= 0; r--) {
            sb.append(r + 1).append("  ");
            for (int f = 0; f < 8; f++) {
                int pc = mailbox[r * 8 + f];
                sb.append(pc == NONE ? '.' : PIECE_CHARS.charAt(pc)).append(' ');
            }
            sb.append('\n');
        }
        sb.append("\n   a b c d e f g h\n");
        sb.append(stm == WHITE ? "White" : "Black").append(" to move\n");
        sb.append("FEN: ").append(toFen()).append('\n');
        return sb.toString();
    }

    /** Prints a bitboard as an 8x8 grid. Handy for checking rays and attack sets. */
    public static String bitboardToString(long bb) {
        StringBuilder sb = new StringBuilder();
        for (int r = 7; r >= 0; r--) {
            sb.append(r + 1).append("  ");
            for (int f = 0; f < 8; f++) {
                sb.append((bb >>> (r * 8 + f) & 1L) != 0 ? "1 " : ". ");
            }
            sb.append('\n');
        }
        sb.append("\n   a b c d e f g h\n");
        return sb.toString();
    }

    // ---------- Accessors ----------
    public long pieces(int color, int type) { return pieces[color][type]; }
    public long occupancy(int color)        { return occ[color]; }
    public long occupancy()                 { return all; }
    public int sideToMove()                 { return stm; }
    public int pieceAt(int sq)              { return mailbox[sq]; }

    // ---------- Perft (move generator correctness test) ----------
    public long perft(int depth) {
        if (depth == 0) return 1;
        int[] moves = new int[256];
        int n = generateMoves(moves);
        long nodes = 0;
        for (int i = 0; i < n; i++) {
            if (makeMove(moves[i])) {
                nodes += perft(depth - 1);
                unmakeMove();
            }
        }
        return nodes;
    }

    /** Per-move node counts at the root, in the style engines print for debugging. */
    public void divide(int depth) {
        int[] moves = new int[256];
        int n = generateMoves(moves);
        long total = 0;
        for (int i = 0; i < n; i++) {
            if (makeMove(moves[i])) {
                long c = perft(depth - 1);
                unmakeMove();
                System.out.println(moveToString(moves[i]) + ": " + c);
                total += c;
            }
        }
        System.out.println("Total: " + total);
    }

    private static void runPerft(String name, String fen, long[] expected) {
        Board b = new Board();
        b.setFen(fen);
        System.out.println("== " + name + " ==");
        for (int d = 1; d <= expected.length; d++) {
            long t = System.nanoTime();
            long nodes = b.perft(d);
            double ms = (System.nanoTime() - t) / 1e6;
            System.out.printf("depth %d: %,d nodes (expected %,d) %s  [%.0f ms]%n",
                    d, nodes, expected[d - 1], nodes == expected[d - 1] ? "OK" : "FAIL", ms);
        }
    }

    private static void check(String name, boolean ok) {
        System.out.println((ok ? "OK    " : "FAIL  ") + name);
    }

    private static void runLegalTests() {
        System.out.println("== Legal move generation ==");
        int[] buf = new int[256];
        Board b = new Board();

        check("start position has 20 legal moves", b.generateLegalMoves(buf) == 20);
        check("parseMove accepts e2e4", b.parseMove("e2e4") != 0);
        check("parseMove rejects e2e5", b.parseMove("e2e5") == 0);

        // Kiwipete: 48 legal moves
        b.setFen("r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1");
        check("Kiwipete has 48 legal moves", b.generateLegalMoves(buf) == 48);

        // Fool's mate: White is checkmated
        b.setFen("rnb1kbnr/pppp1ppp/8/4p3/6Pq/5P2/PPPPP2P/RNBQKBNR w KQkq - 1 3");
        check("fool's mate is checkmate", b.isCheckmate() && b.generateLegalMoves(buf) == 0);

        // Classic stalemate
        b.setFen("7k/5Q2/6K1/8/8/8/8/8 b - - 0 1");
        check("stalemate detected", b.isStalemate() && !b.isCheckmate());

        // Pinned knight must not move: only king moves and rook-file moves are legal
        b.setFen("4r1k1/8/8/8/8/8/4N3/4K3 w - - 0 1");
        boolean knightMoved = false;
        int n = b.generateLegalMoves(buf);
        for (int i = 0; i < n; i++) if (b.pieceAt(from(buf[i])) % 6 == KNIGHT) knightMoved = true;
        check("pinned knight has no legal moves", !knightMoved);

        System.out.println();
    }

    public static void main(String[] args) {
        Board b = new Board();
        System.out.println(b);

        System.out.println("Rook attacks from d4 on an empty board:");
        System.out.println(bitboardToString(rookAttacks(27, 0L)));

        runLegalTests();

        runPerft("Start position",
                "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1",
                new long[] { 20, 400, 8902, 197281, 4865609 });

        runPerft("Kiwipete",
                "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1",
                new long[] { 48, 2039, 97862 });
    }

    public String positionKey() {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'positionKey'");
    }
}
