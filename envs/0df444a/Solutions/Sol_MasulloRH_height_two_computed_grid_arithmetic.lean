-- Prove2me | solution 1 for MasulloRH.height_two_computed_grid_arithmetic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T10:42:50.674494+00:00
-- url     : https://prove2.me/submissions/7b92c99f-46a8-43a3-8b78-7deb34ec8686
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_computed_gaussian_upper_lt_one
import Theorems.Thm_MasulloRH_height_two_remaining_block_bounds
import Definitions.Def_MasulloRH_HeightTwoComputedGrid
import Definitions.Def_MasulloRH_HeightTwoBlockBudgets

import Mathlib.Tactic.IntervalCases

open MasulloRH.ComputedGrid MasulloRH.BlockBudgets
open scoped BigOperators
set_option autoImplicit false

private theorem split_grid (n : ℕ) :
    (∑ j ∈ Finset.range (n*64), energyTerm j) =
      ∑ b ∈ Finset.range n, ∑ j ∈ Finset.range 64, energyTerm (b*64+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,ih]
    exact (Finset.sum_range_succ (fun b => ∑ j ∈ Finset.range 64, energyTerm (b*64+j)) n).symm

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private def groupCap (k : ℕ) : ℚ := ((#[16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 354, 36349, 1180001, 14028621, 66514982, 117489345, 44026243, 67971999, 287820552, 134324819, 136365553, 504659823, 196967032, 185185686, 580550589, 234792831, 244718403, 747589054, 280032079, 422369582, 945954188, 208672114, 478402250, 666755641, 108214291, 309648469, 411605915, 76487511, 534126063, 584767749, 80595833, 300771213, 159405177, 190621746, 583446603, 202744619, 77639595, 178047153, 24782459, 73103543, 96208777, 30822903, 3294757, 116157, 1178, 16, 16, 16, 16, 16, 16, 16] : Array ℕ).getD k 0 : ℕ) / (1099511627776:ℚ)

private def rowCap (k : ℕ) : ℚ := ((#[15095199258753, 15107372292984, 15119523213199, 15131630872543, 15143727390986, 15155794160090, 15167839997543, 15179842082263, 15191835610822, 15203792155353, 15215712661158, 15227613283774, 15239501539528, 15251342082161, 15263168491953, 15274963979782, 15286725489830, 15298481167745, 15310175835464, 15321867595831, 15333543166981, 15345161255379, 15356770213414, 15368351581811, 15379893570530, 15391418915437, 15402904311216, 15414363221009, 15425807844998, 15437223844500, 15448590601799, 15459940662244, 15471265024462, 15482579193810, 15493847019963, 15505084928309, 15516281882491, 15527456403529, 15538631497563, 15549754549769, 15560855945641, 15571922143536, 15582946031641, 15593956371650, 15604959230627, 15615907043861, 15626824393937, 15637735914316, 15648594536590, 15659428027481, 15670236022883, 15681023182729, 15691755242787, 15702488771824, 15713184299794, 15723859474800, 15734467249519, 15745098362934, 15755667528152, 15766199841104, 15776722643941, 15787219373358, 15797662406266, 15808094155973] : Array ℕ).getD k 0 : ℕ) / (18446744073709551616:ℚ)

private theorem g0 : (∑ j ∈ Finset.range 16, cap (0*16+j)) ≤ groupCap 0 := by decide +kernel
private theorem g1 : (∑ j ∈ Finset.range 16, cap (1*16+j)) ≤ groupCap 1 := by decide +kernel
private theorem g2 : (∑ j ∈ Finset.range 16, cap (2*16+j)) ≤ groupCap 2 := by decide +kernel
private theorem g3 : (∑ j ∈ Finset.range 16, cap (3*16+j)) ≤ groupCap 3 := by decide +kernel
private theorem g4 : (∑ j ∈ Finset.range 16, cap (4*16+j)) ≤ groupCap 4 := by decide +kernel
private theorem g5 : (∑ j ∈ Finset.range 16, cap (5*16+j)) ≤ groupCap 5 := by decide +kernel
private theorem g6 : (∑ j ∈ Finset.range 16, cap (6*16+j)) ≤ groupCap 6 := by decide +kernel
private theorem g7 : (∑ j ∈ Finset.range 16, cap (7*16+j)) ≤ groupCap 7 := by decide +kernel
private theorem g8 : (∑ j ∈ Finset.range 16, cap (8*16+j)) ≤ groupCap 8 := by decide +kernel
private theorem g9 : (∑ j ∈ Finset.range 16, cap (9*16+j)) ≤ groupCap 9 := by decide +kernel
private theorem g10 : (∑ j ∈ Finset.range 16, cap (10*16+j)) ≤ groupCap 10 := by decide +kernel
private theorem g11 : (∑ j ∈ Finset.range 16, cap (11*16+j)) ≤ groupCap 11 := by decide +kernel
private theorem g12 : (∑ j ∈ Finset.range 16, cap (12*16+j)) ≤ groupCap 12 := by decide +kernel
private theorem g13 : (∑ j ∈ Finset.range 16, cap (13*16+j)) ≤ groupCap 13 := by decide +kernel
private theorem g14 : (∑ j ∈ Finset.range 16, cap (14*16+j)) ≤ groupCap 14 := by decide +kernel
private theorem g15 : (∑ j ∈ Finset.range 16, cap (15*16+j)) ≤ groupCap 15 := by decide +kernel
private theorem g16 : (∑ j ∈ Finset.range 16, cap (16*16+j)) ≤ groupCap 16 := by decide +kernel
private theorem g17 : (∑ j ∈ Finset.range 16, cap (17*16+j)) ≤ groupCap 17 := by decide +kernel
private theorem g18 : (∑ j ∈ Finset.range 16, cap (18*16+j)) ≤ groupCap 18 := by decide +kernel
private theorem g19 : (∑ j ∈ Finset.range 16, cap (19*16+j)) ≤ groupCap 19 := by decide +kernel
private theorem g20 : (∑ j ∈ Finset.range 16, cap (20*16+j)) ≤ groupCap 20 := by decide +kernel
private theorem g21 : (∑ j ∈ Finset.range 16, cap (21*16+j)) ≤ groupCap 21 := by decide +kernel
private theorem g22 : (∑ j ∈ Finset.range 16, cap (22*16+j)) ≤ groupCap 22 := by decide +kernel
private theorem g23 : (∑ j ∈ Finset.range 16, cap (23*16+j)) ≤ groupCap 23 := by decide +kernel
private theorem g24 : (∑ j ∈ Finset.range 16, cap (24*16+j)) ≤ groupCap 24 := by decide +kernel
private theorem g25 : (∑ j ∈ Finset.range 16, cap (25*16+j)) ≤ groupCap 25 := by decide +kernel
private theorem g26 : (∑ j ∈ Finset.range 16, cap (26*16+j)) ≤ groupCap 26 := by decide +kernel
private theorem g27 : (∑ j ∈ Finset.range 16, cap (27*16+j)) ≤ groupCap 27 := by decide +kernel
private theorem g28 : (∑ j ∈ Finset.range 16, cap (28*16+j)) ≤ groupCap 28 := by decide +kernel
private theorem g29 : (∑ j ∈ Finset.range 16, cap (29*16+j)) ≤ groupCap 29 := by decide +kernel
private theorem g30 : (∑ j ∈ Finset.range 16, cap (30*16+j)) ≤ groupCap 30 := by decide +kernel
private theorem g31 : (∑ j ∈ Finset.range 16, cap (31*16+j)) ≤ groupCap 31 := by decide +kernel
private theorem g32 : (∑ j ∈ Finset.range 16, cap (32*16+j)) ≤ groupCap 32 := by decide +kernel
private theorem g33 : (∑ j ∈ Finset.range 16, cap (33*16+j)) ≤ groupCap 33 := by decide +kernel
private theorem g34 : (∑ j ∈ Finset.range 16, cap (34*16+j)) ≤ groupCap 34 := by decide +kernel
private theorem g35 : (∑ j ∈ Finset.range 16, cap (35*16+j)) ≤ groupCap 35 := by decide +kernel
private theorem g36 : (∑ j ∈ Finset.range 16, cap (36*16+j)) ≤ groupCap 36 := by decide +kernel
private theorem g37 : (∑ j ∈ Finset.range 16, cap (37*16+j)) ≤ groupCap 37 := by decide +kernel
private theorem g38 : (∑ j ∈ Finset.range 16, cap (38*16+j)) ≤ groupCap 38 := by decide +kernel
private theorem g39 : (∑ j ∈ Finset.range 16, cap (39*16+j)) ≤ groupCap 39 := by decide +kernel
private theorem g40 : (∑ j ∈ Finset.range 16, cap (40*16+j)) ≤ groupCap 40 := by decide +kernel
private theorem g41 : (∑ j ∈ Finset.range 16, cap (41*16+j)) ≤ groupCap 41 := by decide +kernel
private theorem g42 : (∑ j ∈ Finset.range 16, cap (42*16+j)) ≤ groupCap 42 := by decide +kernel
private theorem g43 : (∑ j ∈ Finset.range 16, cap (43*16+j)) ≤ groupCap 43 := by decide +kernel
private theorem g44 : (∑ j ∈ Finset.range 16, cap (44*16+j)) ≤ groupCap 44 := by decide +kernel
private theorem g45 : (∑ j ∈ Finset.range 16, cap (45*16+j)) ≤ groupCap 45 := by decide +kernel
private theorem g46 : (∑ j ∈ Finset.range 16, cap (46*16+j)) ≤ groupCap 46 := by decide +kernel
private theorem g47 : (∑ j ∈ Finset.range 16, cap (47*16+j)) ≤ groupCap 47 := by decide +kernel
private theorem g48 : (∑ j ∈ Finset.range 16, cap (48*16+j)) ≤ groupCap 48 := by decide +kernel
private theorem g49 : (∑ j ∈ Finset.range 16, cap (49*16+j)) ≤ groupCap 49 := by decide +kernel
private theorem g50 : (∑ j ∈ Finset.range 16, cap (50*16+j)) ≤ groupCap 50 := by decide +kernel
private theorem g51 : (∑ j ∈ Finset.range 16, cap (51*16+j)) ≤ groupCap 51 := by decide +kernel
private theorem g52 : (∑ j ∈ Finset.range 16, cap (52*16+j)) ≤ groupCap 52 := by decide +kernel
private theorem g53 : (∑ j ∈ Finset.range 16, cap (53*16+j)) ≤ groupCap 53 := by decide +kernel
private theorem g54 : (∑ j ∈ Finset.range 16, cap (54*16+j)) ≤ groupCap 54 := by decide +kernel
private theorem g55 : (∑ j ∈ Finset.range 16, cap (55*16+j)) ≤ groupCap 55 := by decide +kernel
private theorem g56 : (∑ j ∈ Finset.range 16, cap (56*16+j)) ≤ groupCap 56 := by decide +kernel
private theorem g57 : (∑ j ∈ Finset.range 16, cap (57*16+j)) ≤ groupCap 57 := by decide +kernel
private theorem g58 : (∑ j ∈ Finset.range 16, cap (58*16+j)) ≤ groupCap 58 := by decide +kernel
private theorem g59 : (∑ j ∈ Finset.range 16, cap (59*16+j)) ≤ groupCap 59 := by decide +kernel
private theorem g60 : (∑ j ∈ Finset.range 16, cap (60*16+j)) ≤ groupCap 60 := by decide +kernel
private theorem g61 : (∑ j ∈ Finset.range 16, cap (61*16+j)) ≤ groupCap 61 := by decide +kernel
private theorem g62 : (∑ j ∈ Finset.range 16, cap (62*16+j)) ≤ groupCap 62 := by decide +kernel
private theorem g63 : (∑ j ∈ Finset.range 16, cap (63*16+j)) ≤ groupCap 63 := by decide +kernel
private theorem r0 : energyTerm (512*64+0) ≤ rowCap 0 := by decide +kernel
private theorem r1 : energyTerm (512*64+1) ≤ rowCap 1 := by decide +kernel
private theorem r2 : energyTerm (512*64+2) ≤ rowCap 2 := by decide +kernel
private theorem r3 : energyTerm (512*64+3) ≤ rowCap 3 := by decide +kernel
private theorem r4 : energyTerm (512*64+4) ≤ rowCap 4 := by decide +kernel
private theorem r5 : energyTerm (512*64+5) ≤ rowCap 5 := by decide +kernel
private theorem r6 : energyTerm (512*64+6) ≤ rowCap 6 := by decide +kernel
private theorem r7 : energyTerm (512*64+7) ≤ rowCap 7 := by decide +kernel
private theorem r8 : energyTerm (512*64+8) ≤ rowCap 8 := by decide +kernel
private theorem r9 : energyTerm (512*64+9) ≤ rowCap 9 := by decide +kernel
private theorem r10 : energyTerm (512*64+10) ≤ rowCap 10 := by decide +kernel
private theorem r11 : energyTerm (512*64+11) ≤ rowCap 11 := by decide +kernel
private theorem r12 : energyTerm (512*64+12) ≤ rowCap 12 := by decide +kernel
private theorem r13 : energyTerm (512*64+13) ≤ rowCap 13 := by decide +kernel
private theorem r14 : energyTerm (512*64+14) ≤ rowCap 14 := by decide +kernel
private theorem r15 : energyTerm (512*64+15) ≤ rowCap 15 := by decide +kernel
private theorem r16 : energyTerm (512*64+16) ≤ rowCap 16 := by decide +kernel
private theorem r17 : energyTerm (512*64+17) ≤ rowCap 17 := by decide +kernel
private theorem r18 : energyTerm (512*64+18) ≤ rowCap 18 := by decide +kernel
private theorem r19 : energyTerm (512*64+19) ≤ rowCap 19 := by decide +kernel
private theorem r20 : energyTerm (512*64+20) ≤ rowCap 20 := by decide +kernel
private theorem r21 : energyTerm (512*64+21) ≤ rowCap 21 := by decide +kernel
private theorem r22 : energyTerm (512*64+22) ≤ rowCap 22 := by decide +kernel
private theorem r23 : energyTerm (512*64+23) ≤ rowCap 23 := by decide +kernel
private theorem r24 : energyTerm (512*64+24) ≤ rowCap 24 := by decide +kernel
private theorem r25 : energyTerm (512*64+25) ≤ rowCap 25 := by decide +kernel
private theorem r26 : energyTerm (512*64+26) ≤ rowCap 26 := by decide +kernel
private theorem r27 : energyTerm (512*64+27) ≤ rowCap 27 := by decide +kernel
private theorem r28 : energyTerm (512*64+28) ≤ rowCap 28 := by decide +kernel
private theorem r29 : energyTerm (512*64+29) ≤ rowCap 29 := by decide +kernel
private theorem r30 : energyTerm (512*64+30) ≤ rowCap 30 := by decide +kernel
private theorem r31 : energyTerm (512*64+31) ≤ rowCap 31 := by decide +kernel
private theorem r32 : energyTerm (512*64+32) ≤ rowCap 32 := by decide +kernel
private theorem r33 : energyTerm (512*64+33) ≤ rowCap 33 := by decide +kernel
private theorem r34 : energyTerm (512*64+34) ≤ rowCap 34 := by decide +kernel
private theorem r35 : energyTerm (512*64+35) ≤ rowCap 35 := by decide +kernel
private theorem r36 : energyTerm (512*64+36) ≤ rowCap 36 := by decide +kernel
private theorem r37 : energyTerm (512*64+37) ≤ rowCap 37 := by decide +kernel
private theorem r38 : energyTerm (512*64+38) ≤ rowCap 38 := by decide +kernel
private theorem r39 : energyTerm (512*64+39) ≤ rowCap 39 := by decide +kernel
private theorem r40 : energyTerm (512*64+40) ≤ rowCap 40 := by decide +kernel
private theorem r41 : energyTerm (512*64+41) ≤ rowCap 41 := by decide +kernel
private theorem r42 : energyTerm (512*64+42) ≤ rowCap 42 := by decide +kernel
private theorem r43 : energyTerm (512*64+43) ≤ rowCap 43 := by decide +kernel
private theorem r44 : energyTerm (512*64+44) ≤ rowCap 44 := by decide +kernel
private theorem r45 : energyTerm (512*64+45) ≤ rowCap 45 := by decide +kernel
private theorem r46 : energyTerm (512*64+46) ≤ rowCap 46 := by decide +kernel
private theorem r47 : energyTerm (512*64+47) ≤ rowCap 47 := by decide +kernel
private theorem r48 : energyTerm (512*64+48) ≤ rowCap 48 := by decide +kernel
private theorem r49 : energyTerm (512*64+49) ≤ rowCap 49 := by decide +kernel
private theorem r50 : energyTerm (512*64+50) ≤ rowCap 50 := by decide +kernel
private theorem r51 : energyTerm (512*64+51) ≤ rowCap 51 := by decide +kernel
private theorem r52 : energyTerm (512*64+52) ≤ rowCap 52 := by decide +kernel
private theorem r53 : energyTerm (512*64+53) ≤ rowCap 53 := by decide +kernel
private theorem r54 : energyTerm (512*64+54) ≤ rowCap 54 := by decide +kernel
private theorem r55 : energyTerm (512*64+55) ≤ rowCap 55 := by decide +kernel
private theorem r56 : energyTerm (512*64+56) ≤ rowCap 56 := by decide +kernel
private theorem r57 : energyTerm (512*64+57) ≤ rowCap 57 := by decide +kernel
private theorem r58 : energyTerm (512*64+58) ≤ rowCap 58 := by decide +kernel
private theorem r59 : energyTerm (512*64+59) ≤ rowCap 59 := by decide +kernel
private theorem r60 : energyTerm (512*64+60) ≤ rowCap 60 := by decide +kernel
private theorem r61 : energyTerm (512*64+61) ≤ rowCap 61 := by decide +kernel
private theorem r62 : energyTerm (512*64+62) ≤ rowCap 62 := by decide +kernel
private theorem r63 : energyTerm (512*64+63) ≤ rowCap 63 := by decide +kernel

private theorem split_caps (n : ℕ) :
    (∑ j ∈ Finset.range (n*16), cap j) = ∑ b ∈ Finset.range n, ∑ j ∈ Finset.range 16, cap (b*16+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,ih]
    exact (Finset.sum_range_succ (fun b => ∑ j ∈ Finset.range 16, cap (b*16+j)) n).symm

private theorem total_budget : (∑ b ∈ Finset.range 1024, cap b) ≤ (1/100:ℚ) := by
  change (∑ b ∈ Finset.range (64*16), cap b) ≤ _
  rw [split_caps]
  apply le_trans _ (show (∑ i ∈ Finset.range 64, groupCap i) ≤ (1/100:ℚ) by decide +kernel)
  apply Finset.sum_le_sum
  intro b hb
  have h := Finset.mem_range.mp hb
  interval_cases b
  · exact g0
  · exact g1
  · exact g2
  · exact g3
  · exact g4
  · exact g5
  · exact g6
  · exact g7
  · exact g8
  · exact g9
  · exact g10
  · exact g11
  · exact g12
  · exact g13
  · exact g14
  · exact g15
  · exact g16
  · exact g17
  · exact g18
  · exact g19
  · exact g20
  · exact g21
  · exact g22
  · exact g23
  · exact g24
  · exact g25
  · exact g26
  · exact g27
  · exact g28
  · exact g29
  · exact g30
  · exact g31
  · exact g32
  · exact g33
  · exact g34
  · exact g35
  · exact g36
  · exact g37
  · exact g38
  · exact g39
  · exact g40
  · exact g41
  · exact g42
  · exact g43
  · exact g44
  · exact g45
  · exact g46
  · exact g47
  · exact g48
  · exact g49
  · exact g50
  · exact g51
  · exact g52
  · exact g53
  · exact g54
  · exact g55
  · exact g56
  · exact g57
  · exact g58
  · exact g59
  · exact g60
  · exact g61
  · exact g62
  · exact g63

private theorem middle_block : (∑ j ∈ Finset.range 64, energyTerm (512*64+j)) ≤ cap 512 := by
  apply le_trans _ (show (∑ i ∈ Finset.range 64, rowCap i) ≤ cap 512 by decide +kernel)
  apply Finset.sum_le_sum
  intro b hb
  have h := Finset.mem_range.mp hb
  interval_cases b
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11
  · exact r12
  · exact r13
  · exact r14
  · exact r15
  · exact r16
  · exact r17
  · exact r18
  · exact r19
  · exact r20
  · exact r21
  · exact r22
  · exact r23
  · exact r24
  · exact r25
  · exact r26
  · exact r27
  · exact r28
  · exact r29
  · exact r30
  · exact r31
  · exact r32
  · exact r33
  · exact r34
  · exact r35
  · exact r36
  · exact r37
  · exact r38
  · exact r39
  · exact r40
  · exact r41
  · exact r42
  · exact r43
  · exact r44
  · exact r45
  · exact r46
  · exact r47
  · exact r48
  · exact r49
  · exact r50
  · exact r51
  · exact r52
  · exact r53
  · exact r54
  · exact r55
  · exact r56
  · exact r57
  · exact r58
  · exact r59
  · exact r60
  · exact r61
  · exact r62
  · exact r63

theorem solution :
    (∀ k ∈ Finset.Ico (8192:ℤ) 45056,
      (gaussianHi (edge k) (edge (k+1)) (decide (k < 24576))).upper < 1) ∧
    (∑ j ∈ Finset.range 65536, energyTerm j) ≤ (1/100:ℚ) := by
  constructor
  · exact fun k _ => MasulloRH.computed_gaussian_upper_lt_one k
  · change (∑ j ∈ Finset.range (1024*64), energyTerm j) ≤ _
    rw [split_grid]
    apply le_trans _ total_budget
    apply Finset.sum_le_sum
    intro b hb
    by_cases he : b = 512
    · subst b; exact middle_block
    · exact MasulloRH.height_two_remaining_block_bounds b hb he
