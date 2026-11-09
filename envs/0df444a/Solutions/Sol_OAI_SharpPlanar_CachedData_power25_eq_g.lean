-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.power25_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:47:56.762225+00:00
-- url     : https://prove2.me/submissions/ee66ddf8-bd6c-4152-acfe-17037d6a6ab8

import Mathlib
import Definitions.Def_OAIQ098G249
import Definitions.Def_OAIQ098G316
import Theorems.Thm_OAI_SharpPlanar_CachedData_power25_r3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power25_r4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power25_r5_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers30
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
lemma power25_r0_0_eq : ∀ k : Fin 16, power25Expr 0 0 k = power25_r0_0 k := by decide +kernel
lemma power25_r0_1_eq : ∀ k : Fin 16, power25Expr 0 1 k = power25_r0_1 k := by decide +kernel
lemma power25_r0_2_eq : ∀ k : Fin 16, power25Expr 0 2 k = power25_r0_2 k := by decide +kernel
lemma power25_r0_3_eq : ∀ k : Fin 16, power25Expr 0 3 k = power25_r0_3 k := by decide +kernel
lemma power25_r0_4_eq : ∀ k : Fin 16, power25Expr 0 4 k = power25_r0_4 k := by decide +kernel
lemma power25_r0_5_eq : ∀ k : Fin 16, power25Expr 0 5 k = power25_r0_5 k := by decide +kernel
lemma power25_r0_6_eq : ∀ k : Fin 16, power25Expr 0 6 k = power25_r0_6 k := by decide +kernel
lemma power25_r0_7_eq : ∀ k : Fin 16, power25Expr 0 7 k = power25_r0_7 k := by decide +kernel
lemma power25_r0_8_eq : ∀ k : Fin 16, power25Expr 0 8 k = power25_r0_8 k := by decide +kernel
lemma power25_r0_9_eq : ∀ k : Fin 16, power25Expr 0 9 k = power25_r0_9 k := by decide +kernel
lemma power25_r0_10_eq : ∀ k : Fin 16, power25Expr 0 10 k = power25_r0_10 k := by decide +kernel
lemma power25_r0_11_eq : ∀ k : Fin 16, power25Expr 0 11 k = power25_r0_11 k := by decide +kernel
lemma power25_r0_12_eq : ∀ k : Fin 16, power25Expr 0 12 k = power25_r0_12 k := by decide +kernel
lemma power25_r0_13_eq : ∀ k : Fin 16, power25Expr 0 13 k = power25_r0_13 k := by decide +kernel
lemma power25_r0_14_eq : ∀ k : Fin 16, power25Expr 0 14 k = power25_r0_14 k := by decide +kernel
lemma power25_r0_15_eq : ∀ k : Fin 16, power25Expr 0 15 k = power25_r0_15 k := by decide +kernel
lemma power25_r0_eq (i k : Fin 16) : power25Expr 0 i k = power25_r0 i k := by
  fin_cases i
  · exact power25_r0_0_eq k
  · exact power25_r0_1_eq k
  · exact power25_r0_2_eq k
  · exact power25_r0_3_eq k
  · exact power25_r0_4_eq k
  · exact power25_r0_5_eq k
  · exact power25_r0_6_eq k
  · exact power25_r0_7_eq k
  · exact power25_r0_8_eq k
  · exact power25_r0_9_eq k
  · exact power25_r0_10_eq k
  · exact power25_r0_11_eq k
  · exact power25_r0_12_eq k
  · exact power25_r0_13_eq k
  · exact power25_r0_14_eq k
  · exact power25_r0_15_eq k
lemma power25_r1_0_eq : ∀ k : Fin 16, power25Expr 1 0 k = power25_r1_0 k := by decide +kernel
lemma power25_r1_1_eq : ∀ k : Fin 16, power25Expr 1 1 k = power25_r1_1 k := by decide +kernel
lemma power25_r1_2_eq : ∀ k : Fin 16, power25Expr 1 2 k = power25_r1_2 k := by decide +kernel
lemma power25_r1_3_eq : ∀ k : Fin 16, power25Expr 1 3 k = power25_r1_3 k := by decide +kernel
lemma power25_r1_4_eq : ∀ k : Fin 16, power25Expr 1 4 k = power25_r1_4 k := by decide +kernel
lemma power25_r1_5_eq : ∀ k : Fin 16, power25Expr 1 5 k = power25_r1_5 k := by decide +kernel
lemma power25_r1_6_eq : ∀ k : Fin 16, power25Expr 1 6 k = power25_r1_6 k := by decide +kernel
lemma power25_r1_7_eq : ∀ k : Fin 16, power25Expr 1 7 k = power25_r1_7 k := by decide +kernel
lemma power25_r1_8_eq : ∀ k : Fin 16, power25Expr 1 8 k = power25_r1_8 k := by decide +kernel
lemma power25_r1_9_eq : ∀ k : Fin 16, power25Expr 1 9 k = power25_r1_9 k := by decide +kernel
lemma power25_r1_10_eq : ∀ k : Fin 16, power25Expr 1 10 k = power25_r1_10 k := by decide +kernel
lemma power25_r1_11_eq : ∀ k : Fin 16, power25Expr 1 11 k = power25_r1_11 k := by decide +kernel
lemma power25_r1_12_eq : ∀ k : Fin 16, power25Expr 1 12 k = power25_r1_12 k := by decide +kernel
lemma power25_r1_13_eq : ∀ k : Fin 16, power25Expr 1 13 k = power25_r1_13 k := by decide +kernel
lemma power25_r1_14_eq : ∀ k : Fin 16, power25Expr 1 14 k = power25_r1_14 k := by decide +kernel
lemma power25_r1_15_eq : ∀ k : Fin 16, power25Expr 1 15 k = power25_r1_15 k := by decide +kernel
lemma power25_r1_eq (i k : Fin 16) : power25Expr 1 i k = power25_r1 i k := by
  fin_cases i
  · exact power25_r1_0_eq k
  · exact power25_r1_1_eq k
  · exact power25_r1_2_eq k
  · exact power25_r1_3_eq k
  · exact power25_r1_4_eq k
  · exact power25_r1_5_eq k
  · exact power25_r1_6_eq k
  · exact power25_r1_7_eq k
  · exact power25_r1_8_eq k
  · exact power25_r1_9_eq k
  · exact power25_r1_10_eq k
  · exact power25_r1_11_eq k
  · exact power25_r1_12_eq k
  · exact power25_r1_13_eq k
  · exact power25_r1_14_eq k
  · exact power25_r1_15_eq k
lemma power25_r2_0_eq : ∀ k : Fin 16, power25Expr 2 0 k = power25_r2_0 k := by decide +kernel
lemma power25_r2_1_eq : ∀ k : Fin 16, power25Expr 2 1 k = power25_r2_1 k := by decide +kernel
lemma power25_r2_2_eq : ∀ k : Fin 16, power25Expr 2 2 k = power25_r2_2 k := by decide +kernel
lemma power25_r2_3_eq : ∀ k : Fin 16, power25Expr 2 3 k = power25_r2_3 k := by decide +kernel
lemma power25_r2_4_eq : ∀ k : Fin 16, power25Expr 2 4 k = power25_r2_4 k := by decide +kernel
lemma power25_r2_5_eq : ∀ k : Fin 16, power25Expr 2 5 k = power25_r2_5 k := by decide +kernel
lemma power25_r2_6_eq : ∀ k : Fin 16, power25Expr 2 6 k = power25_r2_6 k := by decide +kernel
lemma power25_r2_7_eq : ∀ k : Fin 16, power25Expr 2 7 k = power25_r2_7 k := by decide +kernel
lemma power25_r2_8_eq : ∀ k : Fin 16, power25Expr 2 8 k = power25_r2_8 k := by decide +kernel
lemma power25_r2_9_eq : ∀ k : Fin 16, power25Expr 2 9 k = power25_r2_9 k := by decide +kernel
lemma power25_r2_10_eq : ∀ k : Fin 16, power25Expr 2 10 k = power25_r2_10 k := by decide +kernel
lemma power25_r2_11_eq : ∀ k : Fin 16, power25Expr 2 11 k = power25_r2_11 k := by decide +kernel
lemma power25_r2_12_eq : ∀ k : Fin 16, power25Expr 2 12 k = power25_r2_12 k := by decide +kernel
lemma power25_r2_13_eq : ∀ k : Fin 16, power25Expr 2 13 k = power25_r2_13 k := by decide +kernel
lemma power25_r2_14_eq : ∀ k : Fin 16, power25Expr 2 14 k = power25_r2_14 k := by decide +kernel
lemma power25_r2_15_eq : ∀ k : Fin 16, power25Expr 2 15 k = power25_r2_15 k := by decide +kernel
lemma power25_r2_eq (i k : Fin 16) : power25Expr 2 i k = power25_r2 i k := by
  fin_cases i
  · exact power25_r2_0_eq k
  · exact power25_r2_1_eq k
  · exact power25_r2_2_eq k
  · exact power25_r2_3_eq k
  · exact power25_r2_4_eq k
  · exact power25_r2_5_eq k
  · exact power25_r2_6_eq k
  · exact power25_r2_7_eq k
  · exact power25_r2_8_eq k
  · exact power25_r2_9_eq k
  · exact power25_r2_10_eq k
  · exact power25_r2_11_eq k
  · exact power25_r2_12_eq k
  · exact power25_r2_13_eq k
  · exact power25_r2_14_eq k
  · exact power25_r2_15_eq k
lemma power25_eq_g_oai (j : Fin 6) (i k : Fin 16) : power25Expr j i k = power25 j i k := by
  fin_cases j
  · exact power25_r0_eq i k
  · exact power25_r1_eq i k
  · exact power25_r2_eq i k
  · exact power25_r3_eq_g i k
  · exact power25_r4_eq_g i k
  · exact power25_r5_eq_g i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.power25_eq_g_oai := @OAI.SharpPlanar.CachedData.power25_eq_g_oai
