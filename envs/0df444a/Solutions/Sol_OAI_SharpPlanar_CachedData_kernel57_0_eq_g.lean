-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.kernel57_0_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:59:55.464123+00:00
-- url     : https://prove2.me/submissions/2c57cdf6-a0f4-4561-b985-53b94357bb55

import Mathlib
import Definitions.Def_OAIQ098G1431
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel57_0_r5_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues60
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
lemma kernel57_0_r0_0_eq : ∀ k : Fin 16, kernel57_0Expr 0 0 k = kernel57_0_r0_0 k := by decide +kernel
lemma kernel57_0_r0_1_eq : ∀ k : Fin 16, kernel57_0Expr 0 1 k = kernel57_0_r0_1 k := by decide +kernel
lemma kernel57_0_r0_2_eq : ∀ k : Fin 16, kernel57_0Expr 0 2 k = kernel57_0_r0_2 k := by decide +kernel
lemma kernel57_0_r0_3_eq : ∀ k : Fin 16, kernel57_0Expr 0 3 k = kernel57_0_r0_3 k := by decide +kernel
lemma kernel57_0_r0_4_eq : ∀ k : Fin 16, kernel57_0Expr 0 4 k = kernel57_0_r0_4 k := by decide +kernel
lemma kernel57_0_r0_5_eq : ∀ k : Fin 16, kernel57_0Expr 0 5 k = kernel57_0_r0_5 k := by decide +kernel
lemma kernel57_0_r0_6_eq : ∀ k : Fin 16, kernel57_0Expr 0 6 k = kernel57_0_r0_6 k := by decide +kernel
lemma kernel57_0_r0_7_eq : ∀ k : Fin 16, kernel57_0Expr 0 7 k = kernel57_0_r0_7 k := by decide +kernel
lemma kernel57_0_r0_8_eq : ∀ k : Fin 16, kernel57_0Expr 0 8 k = kernel57_0_r0_8 k := by decide +kernel
lemma kernel57_0_r0_9_eq : ∀ k : Fin 16, kernel57_0Expr 0 9 k = kernel57_0_r0_9 k := by decide +kernel
lemma kernel57_0_r0_10_eq : ∀ k : Fin 16, kernel57_0Expr 0 10 k = kernel57_0_r0_10 k := by decide +kernel
lemma kernel57_0_r0_11_eq : ∀ k : Fin 16, kernel57_0Expr 0 11 k = kernel57_0_r0_11 k := by decide +kernel
lemma kernel57_0_r0_12_eq : ∀ k : Fin 16, kernel57_0Expr 0 12 k = kernel57_0_r0_12 k := by decide +kernel
lemma kernel57_0_r0_13_eq : ∀ k : Fin 16, kernel57_0Expr 0 13 k = kernel57_0_r0_13 k := by decide +kernel
lemma kernel57_0_r0_14_eq : ∀ k : Fin 16, kernel57_0Expr 0 14 k = kernel57_0_r0_14 k := by decide +kernel
lemma kernel57_0_r0_15_eq : ∀ k : Fin 16, kernel57_0Expr 0 15 k = kernel57_0_r0_15 k := by decide +kernel
lemma kernel57_0_r0_eq (i k : Fin 16) : kernel57_0Expr 0 i k = kernel57_0_r0 i k := by
  fin_cases i
  · exact kernel57_0_r0_0_eq k
  · exact kernel57_0_r0_1_eq k
  · exact kernel57_0_r0_2_eq k
  · exact kernel57_0_r0_3_eq k
  · exact kernel57_0_r0_4_eq k
  · exact kernel57_0_r0_5_eq k
  · exact kernel57_0_r0_6_eq k
  · exact kernel57_0_r0_7_eq k
  · exact kernel57_0_r0_8_eq k
  · exact kernel57_0_r0_9_eq k
  · exact kernel57_0_r0_10_eq k
  · exact kernel57_0_r0_11_eq k
  · exact kernel57_0_r0_12_eq k
  · exact kernel57_0_r0_13_eq k
  · exact kernel57_0_r0_14_eq k
  · exact kernel57_0_r0_15_eq k
lemma kernel57_0_r1_0_eq : ∀ k : Fin 16, kernel57_0Expr 1 0 k = kernel57_0_r1_0 k := by decide +kernel
lemma kernel57_0_r1_1_eq : ∀ k : Fin 16, kernel57_0Expr 1 1 k = kernel57_0_r1_1 k := by decide +kernel
lemma kernel57_0_r1_2_eq : ∀ k : Fin 16, kernel57_0Expr 1 2 k = kernel57_0_r1_2 k := by decide +kernel
lemma kernel57_0_r1_3_eq : ∀ k : Fin 16, kernel57_0Expr 1 3 k = kernel57_0_r1_3 k := by decide +kernel
lemma kernel57_0_r1_4_eq : ∀ k : Fin 16, kernel57_0Expr 1 4 k = kernel57_0_r1_4 k := by decide +kernel
lemma kernel57_0_r1_5_eq : ∀ k : Fin 16, kernel57_0Expr 1 5 k = kernel57_0_r1_5 k := by decide +kernel
lemma kernel57_0_r1_6_eq : ∀ k : Fin 16, kernel57_0Expr 1 6 k = kernel57_0_r1_6 k := by decide +kernel
lemma kernel57_0_r1_7_eq : ∀ k : Fin 16, kernel57_0Expr 1 7 k = kernel57_0_r1_7 k := by decide +kernel
lemma kernel57_0_r1_8_eq : ∀ k : Fin 16, kernel57_0Expr 1 8 k = kernel57_0_r1_8 k := by decide +kernel
lemma kernel57_0_r1_9_eq : ∀ k : Fin 16, kernel57_0Expr 1 9 k = kernel57_0_r1_9 k := by decide +kernel
lemma kernel57_0_r1_10_eq : ∀ k : Fin 16, kernel57_0Expr 1 10 k = kernel57_0_r1_10 k := by decide +kernel
lemma kernel57_0_r1_11_eq : ∀ k : Fin 16, kernel57_0Expr 1 11 k = kernel57_0_r1_11 k := by decide +kernel
lemma kernel57_0_r1_12_eq : ∀ k : Fin 16, kernel57_0Expr 1 12 k = kernel57_0_r1_12 k := by decide +kernel
lemma kernel57_0_r1_13_eq : ∀ k : Fin 16, kernel57_0Expr 1 13 k = kernel57_0_r1_13 k := by decide +kernel
lemma kernel57_0_r1_14_eq : ∀ k : Fin 16, kernel57_0Expr 1 14 k = kernel57_0_r1_14 k := by decide +kernel
lemma kernel57_0_r1_15_eq : ∀ k : Fin 16, kernel57_0Expr 1 15 k = kernel57_0_r1_15 k := by decide +kernel
lemma kernel57_0_r1_eq (i k : Fin 16) : kernel57_0Expr 1 i k = kernel57_0_r1 i k := by
  fin_cases i
  · exact kernel57_0_r1_0_eq k
  · exact kernel57_0_r1_1_eq k
  · exact kernel57_0_r1_2_eq k
  · exact kernel57_0_r1_3_eq k
  · exact kernel57_0_r1_4_eq k
  · exact kernel57_0_r1_5_eq k
  · exact kernel57_0_r1_6_eq k
  · exact kernel57_0_r1_7_eq k
  · exact kernel57_0_r1_8_eq k
  · exact kernel57_0_r1_9_eq k
  · exact kernel57_0_r1_10_eq k
  · exact kernel57_0_r1_11_eq k
  · exact kernel57_0_r1_12_eq k
  · exact kernel57_0_r1_13_eq k
  · exact kernel57_0_r1_14_eq k
  · exact kernel57_0_r1_15_eq k
lemma kernel57_0_r2_0_eq : ∀ k : Fin 16, kernel57_0Expr 2 0 k = kernel57_0_r2_0 k := by decide +kernel
lemma kernel57_0_r2_1_eq : ∀ k : Fin 16, kernel57_0Expr 2 1 k = kernel57_0_r2_1 k := by decide +kernel
lemma kernel57_0_r2_2_eq : ∀ k : Fin 16, kernel57_0Expr 2 2 k = kernel57_0_r2_2 k := by decide +kernel
lemma kernel57_0_r2_3_eq : ∀ k : Fin 16, kernel57_0Expr 2 3 k = kernel57_0_r2_3 k := by decide +kernel
lemma kernel57_0_r2_4_eq : ∀ k : Fin 16, kernel57_0Expr 2 4 k = kernel57_0_r2_4 k := by decide +kernel
lemma kernel57_0_r2_5_eq : ∀ k : Fin 16, kernel57_0Expr 2 5 k = kernel57_0_r2_5 k := by decide +kernel
lemma kernel57_0_r2_6_eq : ∀ k : Fin 16, kernel57_0Expr 2 6 k = kernel57_0_r2_6 k := by decide +kernel
lemma kernel57_0_r2_7_eq : ∀ k : Fin 16, kernel57_0Expr 2 7 k = kernel57_0_r2_7 k := by decide +kernel
lemma kernel57_0_r2_8_eq : ∀ k : Fin 16, kernel57_0Expr 2 8 k = kernel57_0_r2_8 k := by decide +kernel
lemma kernel57_0_r2_9_eq : ∀ k : Fin 16, kernel57_0Expr 2 9 k = kernel57_0_r2_9 k := by decide +kernel
lemma kernel57_0_r2_10_eq : ∀ k : Fin 16, kernel57_0Expr 2 10 k = kernel57_0_r2_10 k := by decide +kernel
lemma kernel57_0_r2_11_eq : ∀ k : Fin 16, kernel57_0Expr 2 11 k = kernel57_0_r2_11 k := by decide +kernel
lemma kernel57_0_r2_12_eq : ∀ k : Fin 16, kernel57_0Expr 2 12 k = kernel57_0_r2_12 k := by decide +kernel
lemma kernel57_0_r2_13_eq : ∀ k : Fin 16, kernel57_0Expr 2 13 k = kernel57_0_r2_13 k := by decide +kernel
lemma kernel57_0_r2_14_eq : ∀ k : Fin 16, kernel57_0Expr 2 14 k = kernel57_0_r2_14 k := by decide +kernel
lemma kernel57_0_r2_15_eq : ∀ k : Fin 16, kernel57_0Expr 2 15 k = kernel57_0_r2_15 k := by decide +kernel
lemma kernel57_0_r2_eq (i k : Fin 16) : kernel57_0Expr 2 i k = kernel57_0_r2 i k := by
  fin_cases i
  · exact kernel57_0_r2_0_eq k
  · exact kernel57_0_r2_1_eq k
  · exact kernel57_0_r2_2_eq k
  · exact kernel57_0_r2_3_eq k
  · exact kernel57_0_r2_4_eq k
  · exact kernel57_0_r2_5_eq k
  · exact kernel57_0_r2_6_eq k
  · exact kernel57_0_r2_7_eq k
  · exact kernel57_0_r2_8_eq k
  · exact kernel57_0_r2_9_eq k
  · exact kernel57_0_r2_10_eq k
  · exact kernel57_0_r2_11_eq k
  · exact kernel57_0_r2_12_eq k
  · exact kernel57_0_r2_13_eq k
  · exact kernel57_0_r2_14_eq k
  · exact kernel57_0_r2_15_eq k
lemma kernel57_0_r3_0_eq : ∀ k : Fin 16, kernel57_0Expr 3 0 k = kernel57_0_r3_0 k := by decide +kernel
lemma kernel57_0_r3_1_eq : ∀ k : Fin 16, kernel57_0Expr 3 1 k = kernel57_0_r3_1 k := by decide +kernel
lemma kernel57_0_r3_2_eq : ∀ k : Fin 16, kernel57_0Expr 3 2 k = kernel57_0_r3_2 k := by decide +kernel
lemma kernel57_0_r3_3_eq : ∀ k : Fin 16, kernel57_0Expr 3 3 k = kernel57_0_r3_3 k := by decide +kernel
lemma kernel57_0_r3_4_eq : ∀ k : Fin 16, kernel57_0Expr 3 4 k = kernel57_0_r3_4 k := by decide +kernel
lemma kernel57_0_r3_5_eq : ∀ k : Fin 16, kernel57_0Expr 3 5 k = kernel57_0_r3_5 k := by decide +kernel
lemma kernel57_0_r3_6_eq : ∀ k : Fin 16, kernel57_0Expr 3 6 k = kernel57_0_r3_6 k := by decide +kernel
lemma kernel57_0_r3_7_eq : ∀ k : Fin 16, kernel57_0Expr 3 7 k = kernel57_0_r3_7 k := by decide +kernel
lemma kernel57_0_r3_8_eq : ∀ k : Fin 16, kernel57_0Expr 3 8 k = kernel57_0_r3_8 k := by decide +kernel
lemma kernel57_0_r3_9_eq : ∀ k : Fin 16, kernel57_0Expr 3 9 k = kernel57_0_r3_9 k := by decide +kernel
lemma kernel57_0_r3_10_eq : ∀ k : Fin 16, kernel57_0Expr 3 10 k = kernel57_0_r3_10 k := by decide +kernel
lemma kernel57_0_r3_11_eq : ∀ k : Fin 16, kernel57_0Expr 3 11 k = kernel57_0_r3_11 k := by decide +kernel
lemma kernel57_0_r3_12_eq : ∀ k : Fin 16, kernel57_0Expr 3 12 k = kernel57_0_r3_12 k := by decide +kernel
lemma kernel57_0_r3_13_eq : ∀ k : Fin 16, kernel57_0Expr 3 13 k = kernel57_0_r3_13 k := by decide +kernel
lemma kernel57_0_r3_14_eq : ∀ k : Fin 16, kernel57_0Expr 3 14 k = kernel57_0_r3_14 k := by decide +kernel
lemma kernel57_0_r3_15_eq : ∀ k : Fin 16, kernel57_0Expr 3 15 k = kernel57_0_r3_15 k := by decide +kernel
lemma kernel57_0_r3_eq (i k : Fin 16) : kernel57_0Expr 3 i k = kernel57_0_r3 i k := by
  fin_cases i
  · exact kernel57_0_r3_0_eq k
  · exact kernel57_0_r3_1_eq k
  · exact kernel57_0_r3_2_eq k
  · exact kernel57_0_r3_3_eq k
  · exact kernel57_0_r3_4_eq k
  · exact kernel57_0_r3_5_eq k
  · exact kernel57_0_r3_6_eq k
  · exact kernel57_0_r3_7_eq k
  · exact kernel57_0_r3_8_eq k
  · exact kernel57_0_r3_9_eq k
  · exact kernel57_0_r3_10_eq k
  · exact kernel57_0_r3_11_eq k
  · exact kernel57_0_r3_12_eq k
  · exact kernel57_0_r3_13_eq k
  · exact kernel57_0_r3_14_eq k
  · exact kernel57_0_r3_15_eq k
lemma kernel57_0_r4_0_eq : ∀ k : Fin 16, kernel57_0Expr 4 0 k = kernel57_0_r4_0 k := by decide +kernel
lemma kernel57_0_r4_1_eq : ∀ k : Fin 16, kernel57_0Expr 4 1 k = kernel57_0_r4_1 k := by decide +kernel
lemma kernel57_0_r4_2_eq : ∀ k : Fin 16, kernel57_0Expr 4 2 k = kernel57_0_r4_2 k := by decide +kernel
lemma kernel57_0_r4_3_eq : ∀ k : Fin 16, kernel57_0Expr 4 3 k = kernel57_0_r4_3 k := by decide +kernel
lemma kernel57_0_r4_4_eq : ∀ k : Fin 16, kernel57_0Expr 4 4 k = kernel57_0_r4_4 k := by decide +kernel
lemma kernel57_0_r4_5_eq : ∀ k : Fin 16, kernel57_0Expr 4 5 k = kernel57_0_r4_5 k := by decide +kernel
lemma kernel57_0_r4_6_eq : ∀ k : Fin 16, kernel57_0Expr 4 6 k = kernel57_0_r4_6 k := by decide +kernel
lemma kernel57_0_r4_7_eq : ∀ k : Fin 16, kernel57_0Expr 4 7 k = kernel57_0_r4_7 k := by decide +kernel
lemma kernel57_0_r4_8_eq : ∀ k : Fin 16, kernel57_0Expr 4 8 k = kernel57_0_r4_8 k := by decide +kernel
lemma kernel57_0_r4_9_eq : ∀ k : Fin 16, kernel57_0Expr 4 9 k = kernel57_0_r4_9 k := by decide +kernel
lemma kernel57_0_r4_10_eq : ∀ k : Fin 16, kernel57_0Expr 4 10 k = kernel57_0_r4_10 k := by decide +kernel
lemma kernel57_0_r4_11_eq : ∀ k : Fin 16, kernel57_0Expr 4 11 k = kernel57_0_r4_11 k := by decide +kernel
lemma kernel57_0_r4_12_eq : ∀ k : Fin 16, kernel57_0Expr 4 12 k = kernel57_0_r4_12 k := by decide +kernel
lemma kernel57_0_r4_13_eq : ∀ k : Fin 16, kernel57_0Expr 4 13 k = kernel57_0_r4_13 k := by decide +kernel
lemma kernel57_0_r4_14_eq : ∀ k : Fin 16, kernel57_0Expr 4 14 k = kernel57_0_r4_14 k := by decide +kernel
lemma kernel57_0_r4_15_eq : ∀ k : Fin 16, kernel57_0Expr 4 15 k = kernel57_0_r4_15 k := by decide +kernel
lemma kernel57_0_r4_eq (i k : Fin 16) : kernel57_0Expr 4 i k = kernel57_0_r4 i k := by
  fin_cases i
  · exact kernel57_0_r4_0_eq k
  · exact kernel57_0_r4_1_eq k
  · exact kernel57_0_r4_2_eq k
  · exact kernel57_0_r4_3_eq k
  · exact kernel57_0_r4_4_eq k
  · exact kernel57_0_r4_5_eq k
  · exact kernel57_0_r4_6_eq k
  · exact kernel57_0_r4_7_eq k
  · exact kernel57_0_r4_8_eq k
  · exact kernel57_0_r4_9_eq k
  · exact kernel57_0_r4_10_eq k
  · exact kernel57_0_r4_11_eq k
  · exact kernel57_0_r4_12_eq k
  · exact kernel57_0_r4_13_eq k
  · exact kernel57_0_r4_14_eq k
  · exact kernel57_0_r4_15_eq k
lemma kernel57_0_eq_g_oai (j : Fin 6) (i k : Fin 16) : kernel57_0Expr j i k = kernel57_0 j i k := by
  fin_cases j
  · exact kernel57_0_r0_eq i k
  · exact kernel57_0_r1_eq i k
  · exact kernel57_0_r2_eq i k
  · exact kernel57_0_r3_eq i k
  · exact kernel57_0_r4_eq i k
  · exact kernel57_0_r5_eq_g i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.kernel57_0_eq_g_oai := @OAI.SharpPlanar.CachedData.kernel57_0_eq_g_oai
