-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.power33_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:16:40.905378+00:00
-- url     : https://prove2.me/submissions/68dbd883-528d-4863-90f1-59a333451b05

import Mathlib
import Definitions.Def_OAIQ098G250
import Definitions.Def_OAIQ098G319
import Theorems.Thm_OAI_SharpPlanar_CachedData_power33_r0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power33_r1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power33_r4_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers40
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
lemma power33_r2_0_eq : ∀ k : Fin 16, power33Expr 2 0 k = power33_r2_0 k := by decide +kernel
lemma power33_r2_1_eq : ∀ k : Fin 16, power33Expr 2 1 k = power33_r2_1 k := by decide +kernel
lemma power33_r2_2_eq : ∀ k : Fin 16, power33Expr 2 2 k = power33_r2_2 k := by decide +kernel
lemma power33_r2_3_eq : ∀ k : Fin 16, power33Expr 2 3 k = power33_r2_3 k := by decide +kernel
lemma power33_r2_4_eq : ∀ k : Fin 16, power33Expr 2 4 k = power33_r2_4 k := by decide +kernel
lemma power33_r2_5_eq : ∀ k : Fin 16, power33Expr 2 5 k = power33_r2_5 k := by decide +kernel
lemma power33_r2_6_eq : ∀ k : Fin 16, power33Expr 2 6 k = power33_r2_6 k := by decide +kernel
lemma power33_r2_7_eq : ∀ k : Fin 16, power33Expr 2 7 k = power33_r2_7 k := by decide +kernel
lemma power33_r2_8_eq : ∀ k : Fin 16, power33Expr 2 8 k = power33_r2_8 k := by decide +kernel
lemma power33_r2_9_eq : ∀ k : Fin 16, power33Expr 2 9 k = power33_r2_9 k := by decide +kernel
lemma power33_r2_10_eq : ∀ k : Fin 16, power33Expr 2 10 k = power33_r2_10 k := by decide +kernel
lemma power33_r2_11_eq : ∀ k : Fin 16, power33Expr 2 11 k = power33_r2_11 k := by decide +kernel
lemma power33_r2_12_eq : ∀ k : Fin 16, power33Expr 2 12 k = power33_r2_12 k := by decide +kernel
lemma power33_r2_13_eq : ∀ k : Fin 16, power33Expr 2 13 k = power33_r2_13 k := by decide +kernel
lemma power33_r2_14_eq : ∀ k : Fin 16, power33Expr 2 14 k = power33_r2_14 k := by decide +kernel
lemma power33_r2_15_eq : ∀ k : Fin 16, power33Expr 2 15 k = power33_r2_15 k := by decide +kernel
lemma power33_r2_eq (i k : Fin 16) : power33Expr 2 i k = power33_r2 i k := by
  fin_cases i
  · exact power33_r2_0_eq k
  · exact power33_r2_1_eq k
  · exact power33_r2_2_eq k
  · exact power33_r2_3_eq k
  · exact power33_r2_4_eq k
  · exact power33_r2_5_eq k
  · exact power33_r2_6_eq k
  · exact power33_r2_7_eq k
  · exact power33_r2_8_eq k
  · exact power33_r2_9_eq k
  · exact power33_r2_10_eq k
  · exact power33_r2_11_eq k
  · exact power33_r2_12_eq k
  · exact power33_r2_13_eq k
  · exact power33_r2_14_eq k
  · exact power33_r2_15_eq k
lemma power33_r3_0_eq : ∀ k : Fin 16, power33Expr 3 0 k = power33_r3_0 k := by decide +kernel
lemma power33_r3_1_eq : ∀ k : Fin 16, power33Expr 3 1 k = power33_r3_1 k := by decide +kernel
lemma power33_r3_2_eq : ∀ k : Fin 16, power33Expr 3 2 k = power33_r3_2 k := by decide +kernel
lemma power33_r3_3_eq : ∀ k : Fin 16, power33Expr 3 3 k = power33_r3_3 k := by decide +kernel
lemma power33_r3_4_eq : ∀ k : Fin 16, power33Expr 3 4 k = power33_r3_4 k := by decide +kernel
lemma power33_r3_5_eq : ∀ k : Fin 16, power33Expr 3 5 k = power33_r3_5 k := by decide +kernel
lemma power33_r3_6_eq : ∀ k : Fin 16, power33Expr 3 6 k = power33_r3_6 k := by decide +kernel
lemma power33_r3_7_eq : ∀ k : Fin 16, power33Expr 3 7 k = power33_r3_7 k := by decide +kernel
lemma power33_r3_8_eq : ∀ k : Fin 16, power33Expr 3 8 k = power33_r3_8 k := by decide +kernel
lemma power33_r3_9_eq : ∀ k : Fin 16, power33Expr 3 9 k = power33_r3_9 k := by decide +kernel
lemma power33_r3_10_eq : ∀ k : Fin 16, power33Expr 3 10 k = power33_r3_10 k := by decide +kernel
lemma power33_r3_11_eq : ∀ k : Fin 16, power33Expr 3 11 k = power33_r3_11 k := by decide +kernel
lemma power33_r3_12_eq : ∀ k : Fin 16, power33Expr 3 12 k = power33_r3_12 k := by decide +kernel
lemma power33_r3_13_eq : ∀ k : Fin 16, power33Expr 3 13 k = power33_r3_13 k := by decide +kernel
lemma power33_r3_14_eq : ∀ k : Fin 16, power33Expr 3 14 k = power33_r3_14 k := by decide +kernel
lemma power33_r3_15_eq : ∀ k : Fin 16, power33Expr 3 15 k = power33_r3_15 k := by decide +kernel
lemma power33_r3_eq (i k : Fin 16) : power33Expr 3 i k = power33_r3 i k := by
  fin_cases i
  · exact power33_r3_0_eq k
  · exact power33_r3_1_eq k
  · exact power33_r3_2_eq k
  · exact power33_r3_3_eq k
  · exact power33_r3_4_eq k
  · exact power33_r3_5_eq k
  · exact power33_r3_6_eq k
  · exact power33_r3_7_eq k
  · exact power33_r3_8_eq k
  · exact power33_r3_9_eq k
  · exact power33_r3_10_eq k
  · exact power33_r3_11_eq k
  · exact power33_r3_12_eq k
  · exact power33_r3_13_eq k
  · exact power33_r3_14_eq k
  · exact power33_r3_15_eq k
lemma power33_r5_0_eq : ∀ k : Fin 16, power33Expr 5 0 k = power33_r5_0 k := by decide +kernel
lemma power33_r5_1_eq : ∀ k : Fin 16, power33Expr 5 1 k = power33_r5_1 k := by decide +kernel
lemma power33_r5_2_eq : ∀ k : Fin 16, power33Expr 5 2 k = power33_r5_2 k := by decide +kernel
lemma power33_r5_3_eq : ∀ k : Fin 16, power33Expr 5 3 k = power33_r5_3 k := by decide +kernel
lemma power33_r5_4_eq : ∀ k : Fin 16, power33Expr 5 4 k = power33_r5_4 k := by decide +kernel
lemma power33_r5_5_eq : ∀ k : Fin 16, power33Expr 5 5 k = power33_r5_5 k := by decide +kernel
lemma power33_r5_6_eq : ∀ k : Fin 16, power33Expr 5 6 k = power33_r5_6 k := by decide +kernel
lemma power33_r5_7_eq : ∀ k : Fin 16, power33Expr 5 7 k = power33_r5_7 k := by decide +kernel
lemma power33_r5_8_eq : ∀ k : Fin 16, power33Expr 5 8 k = power33_r5_8 k := by decide +kernel
lemma power33_r5_9_eq : ∀ k : Fin 16, power33Expr 5 9 k = power33_r5_9 k := by decide +kernel
lemma power33_r5_10_eq : ∀ k : Fin 16, power33Expr 5 10 k = power33_r5_10 k := by decide +kernel
lemma power33_r5_11_eq : ∀ k : Fin 16, power33Expr 5 11 k = power33_r5_11 k := by decide +kernel
lemma power33_r5_12_eq : ∀ k : Fin 16, power33Expr 5 12 k = power33_r5_12 k := by decide +kernel
lemma power33_r5_13_eq : ∀ k : Fin 16, power33Expr 5 13 k = power33_r5_13 k := by decide +kernel
lemma power33_r5_14_eq : ∀ k : Fin 16, power33Expr 5 14 k = power33_r5_14 k := by decide +kernel
lemma power33_r5_15_eq : ∀ k : Fin 16, power33Expr 5 15 k = power33_r5_15 k := by decide +kernel
lemma power33_r5_eq (i k : Fin 16) : power33Expr 5 i k = power33_r5 i k := by
  fin_cases i
  · exact power33_r5_0_eq k
  · exact power33_r5_1_eq k
  · exact power33_r5_2_eq k
  · exact power33_r5_3_eq k
  · exact power33_r5_4_eq k
  · exact power33_r5_5_eq k
  · exact power33_r5_6_eq k
  · exact power33_r5_7_eq k
  · exact power33_r5_8_eq k
  · exact power33_r5_9_eq k
  · exact power33_r5_10_eq k
  · exact power33_r5_11_eq k
  · exact power33_r5_12_eq k
  · exact power33_r5_13_eq k
  · exact power33_r5_14_eq k
  · exact power33_r5_15_eq k
lemma power33_eq_g_oai (j : Fin 6) (i k : Fin 16) : power33Expr j i k = power33 j i k := by
  fin_cases j
  · exact power33_r0_eq_g i k
  · exact power33_r1_eq_g i k
  · exact power33_r2_eq i k
  · exact power33_r3_eq i k
  · exact power33_r4_eq_g i k
  · exact power33_r5_eq i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.power33_eq_g_oai := @OAI.SharpPlanar.CachedData.power33_eq_g_oai
