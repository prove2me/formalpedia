-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.power15_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:42:08.916428+00:00
-- url     : https://prove2.me/submissions/506c619a-11ae-4f7f-b50d-650a07e89072

import Mathlib
import Definitions.Def_OAIQ098G241
import Definitions.Def_OAIQ098G311
import Theorems.Thm_OAI_SharpPlanar_CachedData_power15_r0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power15_r1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power15_r5_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers20
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
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power15_r2_0_eq : ∀ k : Fin 16, power15Expr 2 0 k = power15_r2_0 k := by decide +kernel
lemma power15_r2_1_eq : ∀ k : Fin 16, power15Expr 2 1 k = power15_r2_1 k := by decide +kernel
lemma power15_r2_2_eq : ∀ k : Fin 16, power15Expr 2 2 k = power15_r2_2 k := by decide +kernel
lemma power15_r2_3_eq : ∀ k : Fin 16, power15Expr 2 3 k = power15_r2_3 k := by decide +kernel
lemma power15_r2_4_eq : ∀ k : Fin 16, power15Expr 2 4 k = power15_r2_4 k := by decide +kernel
lemma power15_r2_5_eq : ∀ k : Fin 16, power15Expr 2 5 k = power15_r2_5 k := by decide +kernel
lemma power15_r2_6_eq : ∀ k : Fin 16, power15Expr 2 6 k = power15_r2_6 k := by decide +kernel
lemma power15_r2_7_eq : ∀ k : Fin 16, power15Expr 2 7 k = power15_r2_7 k := by decide +kernel
lemma power15_r2_8_eq : ∀ k : Fin 16, power15Expr 2 8 k = power15_r2_8 k := by decide +kernel
lemma power15_r2_9_eq : ∀ k : Fin 16, power15Expr 2 9 k = power15_r2_9 k := by decide +kernel
lemma power15_r2_10_eq : ∀ k : Fin 16, power15Expr 2 10 k = power15_r2_10 k := by decide +kernel
lemma power15_r2_11_eq : ∀ k : Fin 16, power15Expr 2 11 k = power15_r2_11 k := by decide +kernel
lemma power15_r2_12_eq : ∀ k : Fin 16, power15Expr 2 12 k = power15_r2_12 k := by decide +kernel
lemma power15_r2_13_eq : ∀ k : Fin 16, power15Expr 2 13 k = power15_r2_13 k := by decide +kernel
lemma power15_r2_14_eq : ∀ k : Fin 16, power15Expr 2 14 k = power15_r2_14 k := by decide +kernel
lemma power15_r2_15_eq : ∀ k : Fin 16, power15Expr 2 15 k = power15_r2_15 k := by decide +kernel
lemma power15_r2_eq (i k : Fin 16) : power15Expr 2 i k = power15_r2 i k := by
  fin_cases i
  · exact power15_r2_0_eq k
  · exact power15_r2_1_eq k
  · exact power15_r2_2_eq k
  · exact power15_r2_3_eq k
  · exact power15_r2_4_eq k
  · exact power15_r2_5_eq k
  · exact power15_r2_6_eq k
  · exact power15_r2_7_eq k
  · exact power15_r2_8_eq k
  · exact power15_r2_9_eq k
  · exact power15_r2_10_eq k
  · exact power15_r2_11_eq k
  · exact power15_r2_12_eq k
  · exact power15_r2_13_eq k
  · exact power15_r2_14_eq k
  · exact power15_r2_15_eq k
lemma power15_r3_0_eq : ∀ k : Fin 16, power15Expr 3 0 k = power15_r3_0 k := by decide +kernel
lemma power15_r3_1_eq : ∀ k : Fin 16, power15Expr 3 1 k = power15_r3_1 k := by decide +kernel
lemma power15_r3_2_eq : ∀ k : Fin 16, power15Expr 3 2 k = power15_r3_2 k := by decide +kernel
lemma power15_r3_3_eq : ∀ k : Fin 16, power15Expr 3 3 k = power15_r3_3 k := by decide +kernel
lemma power15_r3_4_eq : ∀ k : Fin 16, power15Expr 3 4 k = power15_r3_4 k := by decide +kernel
lemma power15_r3_5_eq : ∀ k : Fin 16, power15Expr 3 5 k = power15_r3_5 k := by decide +kernel
lemma power15_r3_6_eq : ∀ k : Fin 16, power15Expr 3 6 k = power15_r3_6 k := by decide +kernel
lemma power15_r3_7_eq : ∀ k : Fin 16, power15Expr 3 7 k = power15_r3_7 k := by decide +kernel
lemma power15_r3_8_eq : ∀ k : Fin 16, power15Expr 3 8 k = power15_r3_8 k := by decide +kernel
lemma power15_r3_9_eq : ∀ k : Fin 16, power15Expr 3 9 k = power15_r3_9 k := by decide +kernel
lemma power15_r3_10_eq : ∀ k : Fin 16, power15Expr 3 10 k = power15_r3_10 k := by decide +kernel
lemma power15_r3_11_eq : ∀ k : Fin 16, power15Expr 3 11 k = power15_r3_11 k := by decide +kernel
lemma power15_r3_12_eq : ∀ k : Fin 16, power15Expr 3 12 k = power15_r3_12 k := by decide +kernel
lemma power15_r3_13_eq : ∀ k : Fin 16, power15Expr 3 13 k = power15_r3_13 k := by decide +kernel
lemma power15_r3_14_eq : ∀ k : Fin 16, power15Expr 3 14 k = power15_r3_14 k := by decide +kernel
lemma power15_r3_15_eq : ∀ k : Fin 16, power15Expr 3 15 k = power15_r3_15 k := by decide +kernel
lemma power15_r3_eq (i k : Fin 16) : power15Expr 3 i k = power15_r3 i k := by
  fin_cases i
  · exact power15_r3_0_eq k
  · exact power15_r3_1_eq k
  · exact power15_r3_2_eq k
  · exact power15_r3_3_eq k
  · exact power15_r3_4_eq k
  · exact power15_r3_5_eq k
  · exact power15_r3_6_eq k
  · exact power15_r3_7_eq k
  · exact power15_r3_8_eq k
  · exact power15_r3_9_eq k
  · exact power15_r3_10_eq k
  · exact power15_r3_11_eq k
  · exact power15_r3_12_eq k
  · exact power15_r3_13_eq k
  · exact power15_r3_14_eq k
  · exact power15_r3_15_eq k
lemma power15_r4_0_eq : ∀ k : Fin 16, power15Expr 4 0 k = power15_r4_0 k := by decide +kernel
lemma power15_r4_1_eq : ∀ k : Fin 16, power15Expr 4 1 k = power15_r4_1 k := by decide +kernel
lemma power15_r4_2_eq : ∀ k : Fin 16, power15Expr 4 2 k = power15_r4_2 k := by decide +kernel
lemma power15_r4_3_eq : ∀ k : Fin 16, power15Expr 4 3 k = power15_r4_3 k := by decide +kernel
lemma power15_r4_4_eq : ∀ k : Fin 16, power15Expr 4 4 k = power15_r4_4 k := by decide +kernel
lemma power15_r4_5_eq : ∀ k : Fin 16, power15Expr 4 5 k = power15_r4_5 k := by decide +kernel
lemma power15_r4_6_eq : ∀ k : Fin 16, power15Expr 4 6 k = power15_r4_6 k := by decide +kernel
lemma power15_r4_7_eq : ∀ k : Fin 16, power15Expr 4 7 k = power15_r4_7 k := by decide +kernel
lemma power15_r4_8_eq : ∀ k : Fin 16, power15Expr 4 8 k = power15_r4_8 k := by decide +kernel
lemma power15_r4_9_eq : ∀ k : Fin 16, power15Expr 4 9 k = power15_r4_9 k := by decide +kernel
lemma power15_r4_10_eq : ∀ k : Fin 16, power15Expr 4 10 k = power15_r4_10 k := by decide +kernel
lemma power15_r4_11_eq : ∀ k : Fin 16, power15Expr 4 11 k = power15_r4_11 k := by decide +kernel
lemma power15_r4_12_eq : ∀ k : Fin 16, power15Expr 4 12 k = power15_r4_12 k := by decide +kernel
lemma power15_r4_13_eq : ∀ k : Fin 16, power15Expr 4 13 k = power15_r4_13 k := by decide +kernel
lemma power15_r4_14_eq : ∀ k : Fin 16, power15Expr 4 14 k = power15_r4_14 k := by decide +kernel
lemma power15_r4_15_eq : ∀ k : Fin 16, power15Expr 4 15 k = power15_r4_15 k := by decide +kernel
lemma power15_r4_eq (i k : Fin 16) : power15Expr 4 i k = power15_r4 i k := by
  fin_cases i
  · exact power15_r4_0_eq k
  · exact power15_r4_1_eq k
  · exact power15_r4_2_eq k
  · exact power15_r4_3_eq k
  · exact power15_r4_4_eq k
  · exact power15_r4_5_eq k
  · exact power15_r4_6_eq k
  · exact power15_r4_7_eq k
  · exact power15_r4_8_eq k
  · exact power15_r4_9_eq k
  · exact power15_r4_10_eq k
  · exact power15_r4_11_eq k
  · exact power15_r4_12_eq k
  · exact power15_r4_13_eq k
  · exact power15_r4_14_eq k
  · exact power15_r4_15_eq k
lemma power15_eq_g_oai (j : Fin 6) (i k : Fin 16) : power15Expr j i k = power15 j i k := by
  fin_cases j
  · exact power15_r0_eq_g i k
  · exact power15_r1_eq_g i k
  · exact power15_r2_eq i k
  · exact power15_r3_eq i k
  · exact power15_r4_eq i k
  · exact power15_r5_eq_g i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.power15_eq_g_oai := @OAI.SharpPlanar.CachedData.power15_eq_g_oai
