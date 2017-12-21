/**
    Copyright (C) 2014  Shuang Chen

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package cs.threephase;

import static cs.threephase.Moves.*;
import static cs.threephase.Util.*;
import static cs.threephase.Center2.rlmv;
import static cs.threephase.Center2.ctmv;
import static cs.threephase.Center2.ctprun;
import static cs.threephase.Center2.rlrot;
import static cs.threephase.Center1.symmult;
import static cs.threephase.Center1.ctsmv;
import static cs.threephase.Center1.csprun;
import static cs.threephase.Center1.symmove;

import java.util.*;

public class Search {
    static final int PHASE1_SOLUTIONS = 10000;
    static final int PHASE2_ATTEMPTS = 500;
    static final int PHASE2_SOLUTIONS = 100;
    static final int PHASE3_ATTEMPTS = 100;

    static boolean inited = false;

    PriorityQueue<FullCube> p1sols = new PriorityQueue<FullCube>(PHASE2_ATTEMPTS, new FullCube.ValueComparator());

    static int[] count = new int[1];

    int[] move1 = new int[15];
    int[] move2 = new int[20];
    int[] move3 = new int[20];
    int length1 = 0;
    int length2 = 0;
    int maxlength2;
    boolean add1 = false;
    public FullCube c;
    FullCube c1 = new FullCube();
    FullCube c2 = new FullCube();
    Center2 ct2 = new Center2();
    Center3 ct3 = new Center3();
    Edge3 e12 = new Edge3();
    Edge3[] tempe = new Edge3[20];

    cs.min2phase.Search search333 = new cs.min2phase.Search();

    int valid1 = 0;
    String solution = "";

    int p1SolsCnt = 0;
    FullCube[] arr2 = new FullCube[PHASE2_SOLUTIONS];
    int arr2idx = 0;

    public boolean inverse_solution = false;
    public boolean with_rotation = true;

    public Search() {
        for (int i=0; i<20; i++) {
            tempe[i] = new Edge3();
        }
    }

    public synchronized static void init() {
        if (inited) {
            return;
        }
        cs.min2phase.Search.init();

        System.out.println("Initialize Center1 Solver...");

        Center1.initSym();
        Center1.raw2sym = new int[735471];
        Center1.initSym2Raw();
        Center1.createMoveTable();
        Center1.raw2sym = null;
        Center1.createPrun();

        System.out.println("Initialize Center2 Solver...");

        Center2.init();

        System.out.println("Initialize Center3 Solver...");

        Center3.init();

        System.out.println("Initialize Edge3 Solver...");

        Edge3.initMvrot();
        Edge3.initRaw2Sym();
        Edge3.createPrun();

        System.out.println("OK");

        inited = true;
    }

    public String randomMove(Random r) {
        int[] moveseq = new int[40];
        int lm = 36;
        for (int i=0; i<moveseq.length;) {
            int m = r.nextInt(27);
            if (!ckmv[lm][m]) {
                moveseq[i++] = m;
                lm = m;
            }
        }
        System.out.println(tostr(moveseq));
        return solve(moveseq);
    }

    public String randomState(Random r) {
        c = new FullCube(r);
        doSearch();
        return solution;
    }

    public String solution(String facelet) {
        byte[] f = new byte[96];
        for (int i=0; i<96; i++) {
            f[i] = (byte) "URFDLB".indexOf(facelet.charAt(i));
        }
        c = new FullCube(f);
        doSearch();
        return solution;
    }

    public String solve(String scramble) {
        int[] moveseq = tomove(scramble);
        return solve(moveseq);
    }

    public String solve(int[] moveseq) {
        c = new FullCube(moveseq);
        doSearch();
        return solution;
    }

    int totlen = 0;

    boolean phase1_save_solution(int sym, int lm) {
        c1.copy(c);

        for (int i=0; i<length1; i++) {
            c1.move(move1[i]);
        }

        switch (Center1.finish[sym]) {
        case 0 :
            c1.move(fx1);
            c1.move(bx3);
            move1[length1] = fx1;
            move1[length1+1] = bx3;
            add1 = true;
            sym = 19;
            break;
        case 12869 :
            c1.move(ux1);
            c1.move(dx3);
            move1[length1] = ux1;
            move1[length1+1] = dx3;
            add1 = true;
            sym = 34;
            break;
        case 735470 :
            add1 = false;
            sym = 0;
        }

        ct2.set(c1.getCenter(), c1.getEdge().getParity());
        int s2ct = ct2.getct();
        int s2rl = ct2.getrl();
        int ctp = ctprun[(s2ct * 70) + s2rl];

        /* ctp is used to rank the phase1 solutions so that we keep the
         * best 500 (PHASE2_ATTEMPTS) of them.
         *
         * TODO: what is 'ctp'? I think it is an estimate of how many moves
         * phase2 will take to solve the centers? Am guessing ctprun is the
         * centers prune table.
         */
        c1.value = ctp + length1;
        c1.length1 = length1;
        c1.add1 = add1;
        c1.sym = sym;
        p1SolsCnt++;

        FullCube next;

        // This is what limits phase1 to 500 solutions
        if (p1sols.size() < PHASE2_ATTEMPTS) {
            next = new FullCube(c1);
        } else {
            next = p1sols.poll();

            if (next.value > c1.value) {
                next.copy(c1);
            }
        }

        p1sols.add(next);

        return p1SolsCnt == PHASE1_SOLUTIONS;
    }

    boolean phase1_search(int ct, int sym, int maxl, int lm, int depth) {
        // System.out.format("phase1_search: ct %d, sym %d, maxl %d, lm %d, depth %d\n", ct, sym, maxl, lm, depth);

        if (ct == 0 && maxl < 5) {
            if (maxl == 0) {
                return phase1_save_solution(sym, lm);
            } else {
                return false;
            }
        }

        for (int axis = 0; axis < 27; axis += 3) {

            if (axis == lm || axis == (lm - 9) || axis == (lm - 18)) {
                continue;
            }

            for (int power = 0; power < 3; power++) {

                int m = axis + power;

                // Apply a move to the cube
                int ctx = ctsmv[ct][symmove[sym][m]];

                // Get the new prun cost
                int prun = csprun[ctx>>>6];

                if (prun >= maxl) {
                    if (prun > maxl) {
                        break;
                    }
                    continue;
                }

                int symx = symmult[sym][ctx&0x3f];
                ctx>>>=6;
                move1[depth] = m;

                if (phase1_search(ctx, symx, maxl-1, axis, depth+1)) {
                    return true;
                }
            }
        }
        return false;
    }

    boolean phase2_save_solution() {
        c2.copy(c1);

        // Save the moves that got us here
        for (int i = 0; i < length2; i++) {
            c2.move(move2[i]);
        }

        // Checks for parity
        if (!c2.checkEdge()) {
            return false;
        }

        // verifying that the edge parity and corner parity are not going to cause PLL?
        int eparity = e12.set(c2.getEdge());
        ct3.set(c2.getCenter(), eparity ^ c2.getCorner().getParity());
        int ct = ct3.getct();
        int edge = e12.get(10);
        int prun = Edge3.getprun(e12.getsym());

        if (arr2[arr2idx] == null) {
            arr2[arr2idx] = new FullCube(c2);
        } else {
            arr2[arr2idx].copy(c2);
        }

        // dwalton
        // 'value' is f_cost...cost_to_here + cost_to_goal
        // for cost_to_goal it is using the phase3 centers and phase3 edge prune tables
        arr2[arr2idx].value = length1 + length2 + Math.max(prun, Center3.prun[ct]);
        arr2[arr2idx].length2 = length2;
        arr2idx++;

        return arr2idx == arr2.length;
    }

    boolean phase2_search(int ct, int rl, int maxl, int lm, int depth) {

        if (ct==0 && ctprun[rl] == 0 && maxl == 0) {
            return maxl == 0 && phase2_save_solution();
        }

        for (int m=0; m<23; m++) {

            if (ckmv2[lm][m]) {
                m = skipAxis2[m];
                continue;
            }

            int ctx = ctmv[ct][m];
            int rlx = rlmv[rl][m];
            int prun = ctprun[(ctx * 70) + rlx];

            if (prun >= maxl) {
                // TODO what is this doing?
                if (prun > maxl) {
                    m = skipAxis2[m];
                }
                continue;
            }

            move2[depth] = move2std[m];

            if (phase2_search(ctx, rlx, maxl-1, m, depth+1)) {
                return true;
            }
        }
        return false;
    }

    public boolean phase3_search(int edge, int ct, int prun, int maxl, int lm, int depth) {

        if (maxl == 0) {
            return edge == 0 && ct == 0;
        }

        tempe[depth].set(edge);
        for (int m=0; m<17; m++) {
            if (ckmv3[lm][m]) {
                m = skipAxis3[m];
                continue;
            }
            int ctx = Center3.ctmove[ct][m];
            int prun1 = Center3.prun[ctx];
            if (prun1 >= maxl) {
                if (prun1 > maxl && m < 14) {
                    m = skipAxis3[m];
                }
                continue;
            }
            int edgex = Edge3.getmvrot(tempe[depth].edge, m<<3, 10);

            int cord1x = edgex / Edge3.N_RAW;
            int symcord1x = Edge3.raw2sym[cord1x];
            int symx = symcord1x & 0x7;
            symcord1x >>= 3;
            int cord2x = Edge3.getmvrot(tempe[depth].edge, m<<3|symx, 10) % Edge3.N_RAW;

            int prunx = Edge3.getprun(symcord1x * Edge3.N_RAW + cord2x, prun);
            if (prunx >= maxl) {
                if (prunx > maxl && m < 14) {
                    m = skipAxis3[m];
                }
                continue;
            }

            if (phase3_search(edgex, ctx, prunx, maxl - 1, m, depth + 1)) {
                move3[depth] = m;
                return true;
            }
        }
        return false;
    }

    void doSearch() {
        init();
        solution = "";
        int ud = new Center1(c.getCenter(), 0).getsym();
        int fb = new Center1(c.getCenter(), 1).getsym();
        int rl = new Center1(c.getCenter(), 2).getsym();
        int udprun = csprun[ud >> 6];
        int fbprun = csprun[fb >> 6];
        int rlprun = csprun[rl >> 6];

        p1SolsCnt = 0;
        arr2idx = 0;
        p1sols.clear();

        // java -cp .:threephase.jar:twophase.jar solver DRFDFRUFDURDDLLUFLDLLBLULFBUUFRBLBFLLUDDUFRBURBBRBDLLDURFFBBRUFUFDRFURBUDLDBDUFFBUDRRLDRBLFBRRLB
        System.out.println("phase1 ud: " + ud);
        System.out.println("phase1 rl: " + rl);
        System.out.println("phase1 fb: " + fb);
        System.out.println("");

        System.out.println("phase1 'ct' ud >>> 6: " + (ud >>> 6));
        System.out.println("phase1 'ct' rl >>> 6: " + (rl >>> 6));
        System.out.println("phase1 'ct' fb >>> 6: " + (fb >>> 6));
        System.out.println("");

        System.out.println("phase1 'sym' ud & 0x3f: " + (ud & 0x3f));
        System.out.println("phase1 'sym' rl & 0x3f: " + (rl & 0x3f));
        System.out.println("phase1 'sym' fb & 0x3f: " + (fb & 0x3f));
        System.out.println("");

        System.out.println("phase1 init udprun : " + udprun);
        System.out.println("phase1 init rlprun : " + rlprun);
        System.out.println("phase1 init fbprun : " + fbprun);
        System.out.println("");

        length1 = Math.min(Math.min(udprun, fbprun), rlprun);
        System.out.println("phase1 init length1: " + length1);

        /* Use the minimum UD/LR/FB prune cost as the starting value for length1.
         * phase1_search() does a DFS up to length1 moves saving solutions to p1sols along
         * the way. length1 is then incremented and we do another DFS search to
         * gather more phase1 solutions.
         *
         * We collect solutions until we have found 10000 (aka PHASE1_SOLUTIONS) of them.
         * Of these 10k solutions we keep the best 500 (aka PHASE2_ATTEMPTS). Once we have
         * found 10k solutions phase1_search() returns true which is the signal to exit.
         *
         * It appears that these solutions are all for solving only one of the three pairs
         * of sides (so either solves UD, LR or FB)? I do not see how they are taking the
         * other sides into account as only UD, LR, or FB are being passed to phase1_search().
         *
         * One thing really odd here are the "udprun <= length1" checks...these will always
         * be true as udprun, rlprun, and fbprun are never modified and the initial length1
         * is set to the minimum of those three values. I'll leave it as is for now...
         *
         * Something else to note here, phase1 is to stage the LR centers but this also
         * checks to see if it would be better to stage UD or FB instead.
         */
        while (length1 < 100) {

            if ((rlprun <= length1 && phase1_search(rl >>> 6, rl & 0x3f, length1, -1, 0)) ||
                (udprun <= length1 && phase1_search(ud >>> 6, ud & 0x3f, length1, -1, 0)) ||
                (fbprun <= length1 && phase1_search(fb >>> 6, fb & 0x3f, length1, -1, 0))) {
                break;
            }

            System.out.println("phase1 length1 " + length1 + " found " + p1sols.size() + " solutions (for all length1s)");
            length1++;
        }
        // End of phase 1

        FullCube[] p1SolsArr = p1sols.toArray(new FullCube[0]);
        Arrays.sort(p1SolsArr, 0, p1SolsArr.length);
        System.out.println("");

        /* At this point we have 500 of the 'best' phase1 solutions out
         * of the 10k solutions. These are stored in p1SolsArr.
         *
         * Not sure why the do/while is used here...it looks like you could just call
         * the for loop.
         */
        int MAX_LENGTH2 = 9;
        int length12;
        do {
            /* Use the value of the best phase1 solution to initialize length12. I think
             * 'value' is an estimate of how many moves phase2 will take.
             *
             * length12 will increment each time through the loop and will act as a cutoff
             * on how many moves deep to go on DFS searches.
             *
             * Save up to 100 (PHASE2_SOLUTIONS) solutions for phase2, sort them from best
             * to worst where best is the one that has the lowest phase3 prune table cost.
             */
            OUT:
            for (length12 = p1SolsArr[0].value; length12 < 100; length12++) {
                System.out.println("length12: " + length12);

                for (int i=0; i < p1SolsArr.length; i++) {

                    if (p1SolsArr[i].value > length12) {
                        //System.out.println("BREAK(value > length12) phase1_solution #" + i + " value " + p1SolsArr[i].value + ", length1 " + p1SolsArr[i].length1 + "\n");
                        System.out.println(String.format("BREAK(value %d > length12 %d): phase1_solution #%d value %s, length1 %d\n",
                            p1SolsArr[i].value, length12, i, p1SolsArr[i].value, length1));
                        break;
                    }

                    if (length12 - p1SolsArr[i].length1 > MAX_LENGTH2) {
                        System.out.println("SKIP (> MAX_LENGTH2) phase1_solution #" + i + " value " + p1SolsArr[i].value + ", length1 " + p1SolsArr[i].length1);
                        continue;
                    }

                    // System.out.println("KEEP phase1_solution #" + i + " value " + p1SolsArr[i].value + ", length1 " + p1SolsArr[i].length1);
                    c1.copy(p1SolsArr[i]);
                    ct2.set(c1.getCenter(), c1.getEdge().getParity());
                    int s2ct = ct2.getct();
                    int s2rl = ct2.getrl();
                    length1 = p1SolsArr[i].length1;
                    length2 = length12 - p1SolsArr[i].length1;

                    /* length2 is how many moves deep we are willing to go in search of a phase2 solution.
                     * phase2_search() returns true once we have 100 (PHASE2_SOLUTIONS) solutions in arr2.
                     */
                    if (phase2_search(s2ct, s2rl, length2, 28, 0)) {
                        System.out.println("phase2_search() is complete for MAX_LENGTH2 " + MAX_LENGTH2 + ", length12 " + length12);
                        break OUT;
                    }
                }
            }
            MAX_LENGTH2++;
        } while (length12 == 100);
        // End of phase 2

        Arrays.sort(arr2, 0, arr2idx);
        int length123, index = 0;
        int solcnt = 0;

        int MAX_LENGTH3 = 13;
        do {
            OUT2:
            for (length123=arr2[0].value; length123<100; length123++) {
                for (int i=0; i<Math.min(arr2idx, PHASE3_ATTEMPTS); i++) {
                    if (arr2[i].value > length123) {
                        break;
                    }
                    if (length123 - arr2[i].length1 - arr2[i].length2 > MAX_LENGTH3) {
                        continue;
                    }
                    int eparity = e12.set(arr2[i].getEdge());
                    ct3.set(arr2[i].getCenter(), eparity ^ arr2[i].getCorner().getParity());
                    int ct = ct3.getct();
                    int edge = e12.get(10);
                    int prun = Edge3.getprun(e12.getsym());
                    int lm = 20;

                    if (prun <= length123 - arr2[i].length1 - arr2[i].length2
                            && phase3_search(edge, ct, prun, length123 - arr2[i].length1 - arr2[i].length2, lm, 0)) {
                        solcnt++;
    //                    if (solcnt == 5) {
                            index = i;
                            break OUT2;
    //                    }
                    }
                }
            }
            MAX_LENGTH3++;
        } while (length123 == 100);

        FullCube solcube = new FullCube(arr2[index]);
        length1 = solcube.length1;
        length2 = solcube.length2;
        int length3 = length123 - length1 - length2;

        for (int i=0; i<length3; i++) {
            solcube.move(move3std[move3[i]]);
        }
        // cube is now reduced to 3x3x3


        // disable solving 3x3x3 for now...
        /*
        // solve 3x3x3
        String facelet = solcube.to333Facelet();
        String sol = search333.solution(facelet, 21, 1000000, 500, 0);
        int len333 = search333.length();
        if (sol.startsWith("Error")) {
            System.out.println(sol);
            System.out.println(solcube);
            System.out.println(facelet);
            throw new RuntimeException();
        }
        int[] sol333 = tomove(sol);
        for (int i=0; i<sol333.length; i++) {
            solcube.move(sol333[i]);
        }
        */

        solution = solcube.getMoveString(inverse_solution, with_rotation);

        //totlen = length1 + length2 + length3 + len333;
        totlen = length1 + length2 + length3;
        System.out.format("phase1 %d moves, phase2 %d moves, phase3 %d moves, total %d moves\n", length1, length2, length3, totlen);
    }

    public void calc(FullCube s) {
        c = s;
        doSearch();
    }
}
