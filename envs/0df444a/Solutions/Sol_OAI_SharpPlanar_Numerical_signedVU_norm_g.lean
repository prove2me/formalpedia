-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.signedVU_norm_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:19:46.210191+00:00
-- url     : https://prove2.me/submissions/b7a8f280-8cbc-42c3-9d43-f3e7606caa3a

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G099
import Definitions.Def_OAIQ098G128
import Definitions.Def_OAIQ098G129
import Definitions.Def_OAIQ098G160
import Definitions.Def_OAIQ098G185
import Definitions.Def_OAIQ098G321
import Definitions.Def_OAIQ098G332
import Definitions.Def_OAIQ098G344
import Definitions.Def_OAIQ098G362
import Definitions.Def_OAIQ098G370
import Definitions.Def_OAIQ098G371
import Definitions.Def_OAIQ098G372
import Definitions.Def_OAIQ098G373
import Definitions.Def_OAIQ098G374
import Definitions.Def_OAIQ098G375
import Definitions.Def_OAIQ098G378
import Theorems.Thm_OAI_SharpPlanar_CachedData_column21_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel4_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel4_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_cachedMomentRuleBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_K_column_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_S_column_value_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U100_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U100_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U12_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U12_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U13_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U13_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U15_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U15_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U16_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U16_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U19_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U19_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry0_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry0_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry1_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry1_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry2_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry3_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry3_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry4_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry4_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry5_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_entry5_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U24_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U24_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U25_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U25_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U27_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U27_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U28_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U28_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U31_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U31_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U33_wuminus_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U33_wuplus_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U36_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U36_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U37_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U37_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U39_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U39_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U40_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U40_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U43_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U43_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U45_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U45_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U49_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U49_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U51_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U51_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U52_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U52_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U55_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U55_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U57_wuminus_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U57_wuplus_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U60_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U60_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U61_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U61_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U63_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U63_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U64_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U64_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U67_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U67_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U69_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U69_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U7_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U7_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U72_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U72_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U73_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U73_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U75_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U75_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U76_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U76_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U79_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U79_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U81_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U81_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U84_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U84_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U85_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U85_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U87_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U87_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U88_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U88_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U9_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U9_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U91_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U91_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U93_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U93_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U96_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U96_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U97_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U97_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U99_wuminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_U99_wuplus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_centralIndex_injective_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectminus_column_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectplus_column_g
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace cm21_4_0_0
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
lemma checked : cachedMomentRuleBox column21_0 kernel4_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 21 4 false false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_g column21_0_contains_g kernel4_0_contains_g
end cm21_4_0_0
namespace cm21_4_0_1
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
lemma checked : cachedMomentRuleBox column21_0 kernel4_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 21 4 false true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_g column21_0_contains_g kernel4_1_contains_g
end cm21_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals
open scoped BigOperators

lemma sumBox_contains {ι : Type*} [Fintype ι] {a : ι → RBox} {x : ι → ℝ}
    (ha : ∀ i, (a i).Contains (x i)) : (sumBox a).Contains (∑ i, x i) := by
  constructor
  · simpa only [sumBox,Int.cast_sum,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => (ha i).1)
  · simpa only [sumBox,Int.cast_sum,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => (ha i).2)

lemma matrixMulBox_contains {n m k : ℕ} {a : Matrix (Fin n) (Fin m) RBox}
    {b : Matrix (Fin m) (Fin k) RBox} {A : Matrix (Fin n) (Fin m) ℝ}
    {B : Matrix (Fin m) (Fin k) ℝ} (ha : ∀ i j, (a i j).Contains (A i j))
    (hb : ∀ i j, (b i j).Contains (B i j)) (i j) :
    (matrixMulBox a b i j).Contains ((A*B) i j) := by
  exact sumBox_contains (fun l => RBox.contains_mul_g (ha i l) (hb l j))

lemma column_bound_lt {n m : ℕ} {a : Matrix (Fin n) (Fin m) RBox}
    {A : Matrix (Fin n) (Fin m) ℝ} {u v : ℤ} (hv : 0 < v)
    (ha : ∀ i j, (a i j).Contains (A i j))
    (hc : ∀ j, (∑ i, (a i j).bound)*v < precision*u) :
    ∀ j, ∑ i, |A i j| < (u:ℝ)/v := by
  intro j
  have h₁ : (precision:ℝ)*(∑ i, |A i j|) ≤ (∑ i, ((a i j).bound:ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => RBox.abs_bound_g (ha i j)
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have h₂ : (∑ i, ((a i j).bound:ℝ))*(v:ℝ) < (precision:ℝ)*u := by
    exact_mod_cast hc j
  apply (mul_lt_mul_iff_right₀ precision_pos_g).mp
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hv').mpr
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h₁ hv'.le) h₂

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals
open scoped BigOperators
lemma WplusBox_contains (i j : Fin 6) : (WplusBox i j).Contains (Wplus i j) := RBox.contains_rat_g _ _ (by norm_num)
lemma WminusBox_contains (i j : Fin 6) : (WminusBox i j).Contains (Wminus i j) := RBox.contains_rat_g _ _ (by norm_num)
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical.U21
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma entry2_0_contains : entry2_0.Contains (umat 2 0) := by
  have h0 := K_column_contains_g (n:=node) (m:=4) (by decide) (by decide) false false cm21_4_0_0.contains
  have h1 := K_column_contains_g (n:=node) (m:=4) (by decide) (by decide) false true cm21_4_0_1.contains
  have hh := S_column_value_contains_g (m:=node4) h0
  change entry2_0.Contains (S (columnVector node false) (node4,false))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  decide +kernel
lemma entries_contains (i : Fin 6) (j : Fin 2) : (entries i j).Contains (umat i j) := by
  fin_cases i <;> fin_cases j
  · exact entry0_0_contains_g
  · exact entry0_1_contains_g
  · exact entry1_0_contains_g
  · exact entry1_1_contains_g
  · exact entry2_0_contains
  · exact entry2_1_contains_g
  · exact entry3_0_contains_g
  · exact entry3_1_contains_g
  · exact entry4_0_contains_g
  · exact entry4_1_contains_g
  · exact entry5_0_contains_g
  · exact entry5_1_contains_g
lemma wuplus_contains (i : Fin 6) (j : Fin 2) : (wuplusBox i j).Contains ((Wplus*umat) i j) := matrixMulBox_contains WplusBox_contains entries_contains i j
lemma wuplus_column (j : Fin 2) : ∑ i, |((Wplus*umat) i j)| < (25:ℝ)/100 := by
  have hh := column_bound_lt (u:=25) (v:=100) (a:=wuplusBox) (by norm_num) wuplus_contains (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
lemma wuminus_contains (i : Fin 6) (j : Fin 2) : (wuminusBox i j).Contains ((Wminus*umat) i j) := matrixMulBox_contains WminusBox_contains entries_contains i j
lemma wuminus_column (j : Fin 2) : ∑ i, |((Wminus*umat) i j)| < (17:ℝ)/100 := by
  have hh := column_bound_lt (u:=17) (v:=100) (a:=wuminusBox) (by norm_num) wuminus_contains (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
end SharpPlanar.Numerical.U21

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical.U33
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma wuplus_column (j : Fin 2) : ∑ i, |((Wplus*umat) i j)| < (25:ℝ)/100 := by
  have hh := column_bound_lt (u:=25) (v:=100) (a:=wuplusBox) (by norm_num) wuplus_contains_g (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
lemma wuminus_column (j : Fin 2) : ∑ i, |((Wminus*umat) i j)| < (17:ℝ)/100 := by
  have hh := column_bound_lt (u:=17) (v:=100) (a:=wuminusBox) (by norm_num) wuminus_contains_g (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
end SharpPlanar.Numerical.U33

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical.U57
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma wuplus_column (j : Fin 2) : ∑ i, |((Wplus*umat) i j)| < (25:ℝ)/100 := by
  have hh := column_bound_lt (u:=25) (v:=100) (a:=wuplusBox) (by norm_num) wuplus_contains_g (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
lemma wuminus_column (j : Fin 2) : ∑ i, |((Wminus*umat) i j)| < (17:ℝ)/100 := by
  have hh := column_bound_lt (u:=17) (v:=100) (a:=wuminusBox) (by norm_num) wuminus_contains_g (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
end SharpPlanar.Numerical.U57

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq ι] in
lemma matrixL1_apply (A : Matrix ι κ ℝ) (x : L1Finite κ) (i : ι) :
    matrixL1 A x i = ∑ j, A i j*x j := rfl

omit [DecidableEq ι] in
lemma matrixL1_mul (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    matrixL1 (A*B) = (matrixL1 A).comp (matrixL1 B) := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toLpLin 1 1 (A*B) x = Matrix.toLpLin 1 1 A (Matrix.toLpLin 1 1 B x)
  rw [Matrix.toLpLin_mul (q:=1)]
  rfl
omit [DecidableEq ι] in
lemma matrixL1_sub (A B : Matrix ι κ ℝ) :
    matrixL1 (A-B) = matrixL1 A-matrixL1 B := by
  ext x i
  simp [matrixL1_apply,sub_mul,Finset.sum_sub_distrib]
lemma matrixL1_one : matrixL1 (1:Matrix ι ι ℝ) = 1 := by
  ext x i
  simp [matrixL1_apply,Matrix.one_apply]

omit [DecidableEq ι] in
lemma matrixL1_norm_le {A : Matrix ι κ ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ j, ∑ i, |A i j| ≤ b) : ‖matrixL1 A‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  rw [l1Finite_norm_g,l1Finite_norm_g,Finset.mul_sum]
  calc
    ∑ i, |matrixL1 A x i| ≤ ∑ i, ∑ j, |A i j| * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrixL1_apply]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => A i j*x j) Finset.univ
    _ = ∑ j, (∑ i, |A i j|)* |x j| := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, b* |x j| := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _)

omit [DecidableEq ι] in
lemma matrixL1_norm_lt [Nonempty κ] {A : Matrix ι κ ℝ} {b : ℝ}
    (hA : ∀ j, ∑ i, |A i j| < b) : ‖matrixL1 A‖ < b := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun j : κ => ∑ i, |A i j|) Finset.univ_nonempty
  exact (matrixL1_norm_le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    (fun k => hj k (Finset.mem_univ _))).trans_lt (hA j)
end

section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma approximate_inverse_estimate (A W : E →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) (x : E) :
    ‖x‖ ≤ ‖W (A x)‖/(1-δ) := by
  have he : x = W (A x)+(1-W*A) x := by simp
  have hx : ‖x‖ ≤ ‖W (A x)‖+δ*‖x‖ := calc
    _ = ‖W (A x)+(1-W*A) x‖ := congrArg norm he
    _ ≤ ‖W (A x)‖+‖(1-W*A) x‖ := norm_add_le _ _
    _ ≤ ‖W (A x)‖+δ*‖x‖ := add_le_add le_rfl ((1-W*A).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _)))
  apply (le_div_iff₀ (by linarith : 0 < 1-δ)).mpr
  nlinarith
end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteRestriction_apply (x : X) (i : ι) : finiteRestriction e he x i = x (e i) := rfl
end
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  (e : ι → Node × Bool) (he : Function.Injective e)
  (f : κ → Node × Bool)
lemma compressed_S_matrix :
    (finiteRestriction e he).comp (S.comp (finiteEmbedding f)) =
      matrixL1 (fun i j => S (lp.single 1 (f j) 1) (e i)) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply,finiteRestriction_apply]
  change S (∑ j, lp.single 1 (f j) (x j)) (e i) = _
  rw [map_sum]
  simp only [lp.coeFn_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (lp.single 1 (f j) (x j) : X) = (x j) • (lp.single 1 (f j) 1 : X) := by
    rw [← lp.single_smul]; simp
  rw [hs,map_smul]
  change x j * S (lp.single 1 (f j) 1) (e i) = S (lp.single 1 (f j) 1) (e i) * x j
  ring
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma certified_inverse_comp_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A W : E →L[ℝ] E) (U : F →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) :
    ‖((certifiedEquiv A W (h.trans_lt hd)).symm.toContinuousLinearMap).comp U‖ ≤
      ‖W.comp U‖/(1-δ) := by
  have hd0 : 0 < 1-δ := sub_pos.mpr hd
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hd0.le)
  intro x
  have he : A ((certifiedEquiv A W (h.trans_lt hd)).symm (U x)) = U x :=
    (certifiedEquiv A W (h.trans_lt hd)).apply_symm_apply _
  calc
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm (U x)‖ ≤
        ‖W (A ((certifiedEquiv A W (h.trans_lt hd)).symm (U x)))‖/(1-δ) :=
      approximate_inverse_estimate A W hd h _
    _ = ‖W (U x)‖/(1-δ) := by rw [he]
    _ ≤ (‖W.comp U‖*‖x‖)/(1-δ) := div_le_div_of_nonneg_right ((W.comp U).le_opNorm x) hd0.le
    _ = (‖W.comp U‖/(1-δ))*‖x‖ := by ring
end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse bounds for the central interpolation block

Exact rational approximate inverses give bounds for the two central blocks.
-/

namespace SharpPlanar.Numerical
lemma defectplus_norm : ‖1-(matrixL1 Wplus)*(matrixL1 Aplus)‖ < (1:ℝ)/1000 := by
  have hh := matrixL1_norm_lt defectplus_column_g
  rw [matrixL1_sub,matrixL1_one,matrixL1_mul] at hh
  exact hh
lemma defectminus_norm : ‖1-(matrixL1 Wminus)*(matrixL1 Aminus)‖ < (1:ℝ)/1000 := by
  have hh := matrixL1_norm_lt defectminus_column_g
  rw [matrixL1_sub,matrixL1_one,matrixL1_mul] at hh
  exact hh
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exterior coupling in the finite interpolation system

Column estimates control the coupling between the central and exterior coordinates.
-/

namespace SharpPlanar.Numerical
open scoped BigOperators
lemma WUplus_column (j : Fin 48 × Fin 2) : ∑ i, |((Wplus*Umat) i j)| < (354:ℝ)/100 := by
  rcases j with ⟨n,d⟩
  fin_cases n
  · change ∑ i, |((Wplus*U7.umat) i d)| < (354:ℝ)/100
    exact (U7.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U9.umat) i d)| < (354:ℝ)/100
    exact (U9.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U12.umat) i d)| < (354:ℝ)/100
    exact (U12.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U13.umat) i d)| < (354:ℝ)/100
    exact (U13.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U15.umat) i d)| < (354:ℝ)/100
    exact (U15.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U16.umat) i d)| < (354:ℝ)/100
    exact (U16.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U19.umat) i d)| < (354:ℝ)/100
    exact (U19.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U21.umat) i d)| < (354:ℝ)/100
    exact (U21.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U24.umat) i d)| < (354:ℝ)/100
    exact (U24.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U25.umat) i d)| < (354:ℝ)/100
    exact (U25.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U27.umat) i d)| < (354:ℝ)/100
    exact (U27.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U28.umat) i d)| < (354:ℝ)/100
    exact (U28.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U31.umat) i d)| < (354:ℝ)/100
    exact (U31.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U33.umat) i d)| < (354:ℝ)/100
    exact (U33.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U36.umat) i d)| < (354:ℝ)/100
    exact (U36.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U37.umat) i d)| < (354:ℝ)/100
    exact (U37.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U39.umat) i d)| < (354:ℝ)/100
    exact (U39.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U40.umat) i d)| < (354:ℝ)/100
    exact (U40.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U43.umat) i d)| < (354:ℝ)/100
    exact (U43.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U45.umat) i d)| < (354:ℝ)/100
    exact (U45.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U48.umat) i d)| < (354:ℝ)/100
    exact (U48.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U49.umat) i d)| < (354:ℝ)/100
    exact (U49.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U51.umat) i d)| < (354:ℝ)/100
    exact (U51.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U52.umat) i d)| < (354:ℝ)/100
    exact (U52.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U55.umat) i d)| < (354:ℝ)/100
    exact (U55.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U57.umat) i d)| < (354:ℝ)/100
    exact (U57.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U60.umat) i d)| < (354:ℝ)/100
    exact (U60.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U61.umat) i d)| < (354:ℝ)/100
    exact (U61.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U63.umat) i d)| < (354:ℝ)/100
    exact (U63.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U64.umat) i d)| < (354:ℝ)/100
    exact (U64.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U67.umat) i d)| < (354:ℝ)/100
    exact (U67.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U69.umat) i d)| < (354:ℝ)/100
    exact (U69.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U72.umat) i d)| < (354:ℝ)/100
    exact (U72.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U73.umat) i d)| < (354:ℝ)/100
    exact (U73.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U75.umat) i d)| < (354:ℝ)/100
    exact (U75.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U76.umat) i d)| < (354:ℝ)/100
    exact (U76.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U79.umat) i d)| < (354:ℝ)/100
    exact (U79.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U81.umat) i d)| < (354:ℝ)/100
    exact (U81.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U84.umat) i d)| < (354:ℝ)/100
    exact (U84.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U85.umat) i d)| < (354:ℝ)/100
    exact (U85.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U87.umat) i d)| < (354:ℝ)/100
    exact (U87.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U88.umat) i d)| < (354:ℝ)/100
    exact (U88.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U91.umat) i d)| < (354:ℝ)/100
    exact (U91.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U93.umat) i d)| < (354:ℝ)/100
    exact (U93.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U96.umat) i d)| < (354:ℝ)/100
    exact (U96.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U97.umat) i d)| < (354:ℝ)/100
    exact (U97.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U99.umat) i d)| < (354:ℝ)/100
    exact (U99.wuplus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U100.umat) i d)| < (354:ℝ)/100
    exact (U100.wuplus_column_g d).trans_le (by norm_num)
lemma WUplus_norm : ‖(matrixL1 Wplus).comp (matrixL1 Umat)‖ < (354:ℝ)/100 := by
  rw [← matrixL1_mul]
  exact matrixL1_norm_lt WUplus_column
lemma inversePlus_U_norm : ‖inversePlusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ < (37:ℝ)/10 := by
  have hh := certified_inverse_comp_norm_le (matrixL1 Aplus) (matrixL1 Wplus) (matrixL1 Umat)
    (by norm_num : (1:ℝ)/1000 < 1) defectplus_norm.le
  change ‖inversePlusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [WUplus_norm]
lemma WUminus_column (j : Fin 48 × Fin 2) : ∑ i, |((Wminus*Umat) i j)| < (73:ℝ)/100 := by
  rcases j with ⟨n,d⟩
  fin_cases n
  · change ∑ i, |((Wminus*U7.umat) i d)| < (73:ℝ)/100
    exact (U7.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U9.umat) i d)| < (73:ℝ)/100
    exact (U9.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U12.umat) i d)| < (73:ℝ)/100
    exact (U12.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U13.umat) i d)| < (73:ℝ)/100
    exact (U13.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U15.umat) i d)| < (73:ℝ)/100
    exact (U15.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U16.umat) i d)| < (73:ℝ)/100
    exact (U16.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U19.umat) i d)| < (73:ℝ)/100
    exact (U19.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U21.umat) i d)| < (73:ℝ)/100
    exact (U21.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U24.umat) i d)| < (73:ℝ)/100
    exact (U24.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U25.umat) i d)| < (73:ℝ)/100
    exact (U25.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U27.umat) i d)| < (73:ℝ)/100
    exact (U27.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U28.umat) i d)| < (73:ℝ)/100
    exact (U28.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U31.umat) i d)| < (73:ℝ)/100
    exact (U31.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U33.umat) i d)| < (73:ℝ)/100
    exact (U33.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U36.umat) i d)| < (73:ℝ)/100
    exact (U36.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U37.umat) i d)| < (73:ℝ)/100
    exact (U37.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U39.umat) i d)| < (73:ℝ)/100
    exact (U39.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U40.umat) i d)| < (73:ℝ)/100
    exact (U40.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U43.umat) i d)| < (73:ℝ)/100
    exact (U43.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U45.umat) i d)| < (73:ℝ)/100
    exact (U45.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U48.umat) i d)| < (73:ℝ)/100
    exact (U48.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U49.umat) i d)| < (73:ℝ)/100
    exact (U49.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U51.umat) i d)| < (73:ℝ)/100
    exact (U51.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U52.umat) i d)| < (73:ℝ)/100
    exact (U52.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U55.umat) i d)| < (73:ℝ)/100
    exact (U55.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U57.umat) i d)| < (73:ℝ)/100
    exact (U57.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U60.umat) i d)| < (73:ℝ)/100
    exact (U60.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U61.umat) i d)| < (73:ℝ)/100
    exact (U61.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U63.umat) i d)| < (73:ℝ)/100
    exact (U63.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U64.umat) i d)| < (73:ℝ)/100
    exact (U64.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U67.umat) i d)| < (73:ℝ)/100
    exact (U67.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U69.umat) i d)| < (73:ℝ)/100
    exact (U69.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U72.umat) i d)| < (73:ℝ)/100
    exact (U72.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U73.umat) i d)| < (73:ℝ)/100
    exact (U73.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U75.umat) i d)| < (73:ℝ)/100
    exact (U75.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U76.umat) i d)| < (73:ℝ)/100
    exact (U76.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U79.umat) i d)| < (73:ℝ)/100
    exact (U79.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U81.umat) i d)| < (73:ℝ)/100
    exact (U81.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U84.umat) i d)| < (73:ℝ)/100
    exact (U84.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U85.umat) i d)| < (73:ℝ)/100
    exact (U85.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U87.umat) i d)| < (73:ℝ)/100
    exact (U87.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U88.umat) i d)| < (73:ℝ)/100
    exact (U88.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U91.umat) i d)| < (73:ℝ)/100
    exact (U91.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U93.umat) i d)| < (73:ℝ)/100
    exact (U93.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U96.umat) i d)| < (73:ℝ)/100
    exact (U96.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U97.umat) i d)| < (73:ℝ)/100
    exact (U97.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U99.umat) i d)| < (73:ℝ)/100
    exact (U99.wuminus_column_g d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U100.umat) i d)| < (73:ℝ)/100
    exact (U100.wuminus_column_g d).trans_le (by norm_num)
lemma WUminus_norm : ‖(matrixL1 Wminus).comp (matrixL1 Umat)‖ < (73:ℝ)/100 := by
  rw [← matrixL1_mul]
  exact matrixL1_norm_lt WUminus_column
lemma inverseMinus_U_norm : ‖inverseMinusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ < (37:ℝ)/10 := by
  have hh := certified_inverse_comp_norm_le (matrixL1 Aminus) (matrixL1 Wminus) (matrixL1 Umat)
    (by norm_num : (1:ℝ)/1000 < 1) defectminus_norm.le
  change ‖inverseMinusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [WUminus_norm]
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite interpolation system

Schur complements give existence, uniqueness and norm bounds for the finite system.
-/

namespace SharpPlanar.Numerical
lemma compressed_U : RJ.comp (S.comp IE) = matrixL1 Umat := by
  rw [compressed_S_matrix]; rfl
lemma signedVU_norm_g_oai (neg : Bool) : ‖(centralV neg).comp (signedU neg)‖ ≤ (37:ℝ)/10 := by
  cases neg
  · exact (by simpa only [centralV,signedU,signedS,Bool.false_eq_true,ite_false, if_false,compressed_U] using inversePlus_U_norm.le)
  · simpa only [centralV,signedU,signedS,ite_true, if_true,ContinuousLinearMap.neg_comp,
      ContinuousLinearMap.comp_neg,compressed_U,norm_neg] using inverseMinus_U_norm.le
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.signedVU_norm_g_oai := @OAI.SharpPlanar.Numerical.signedVU_norm_g_oai
