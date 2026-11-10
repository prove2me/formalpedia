-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.kernel15_0_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T06:17:22.044813+00:00
-- url     : https://prove2.me/submissions/4503916c-c3e2-4b19-950a-8bcd19a20929

import Mathlib
import Definitions.Def_OAIQ098G121
import Definitions.Def_OAIQ098G302
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel15_0_r2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel15_0_r3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel15_0_r4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel15_0_r5_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues20
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
lemma kernel15_0_r0_0_eq : ∀ k : Fin 16, kernel15_0Expr 0 0 k = kernel15_0_r0_0 k := by decide +kernel
lemma kernel15_0_r0_1_eq : ∀ k : Fin 16, kernel15_0Expr 0 1 k = kernel15_0_r0_1 k := by decide +kernel
lemma kernel15_0_r0_2_eq : ∀ k : Fin 16, kernel15_0Expr 0 2 k = kernel15_0_r0_2 k := by decide +kernel
lemma kernel15_0_r0_3_eq : ∀ k : Fin 16, kernel15_0Expr 0 3 k = kernel15_0_r0_3 k := by decide +kernel
lemma kernel15_0_r0_4_eq : ∀ k : Fin 16, kernel15_0Expr 0 4 k = kernel15_0_r0_4 k := by decide +kernel
lemma kernel15_0_r0_5_eq : ∀ k : Fin 16, kernel15_0Expr 0 5 k = kernel15_0_r0_5 k := by decide +kernel
lemma kernel15_0_r0_6_eq : ∀ k : Fin 16, kernel15_0Expr 0 6 k = kernel15_0_r0_6 k := by decide +kernel
lemma kernel15_0_r0_7_eq : ∀ k : Fin 16, kernel15_0Expr 0 7 k = kernel15_0_r0_7 k := by decide +kernel
lemma kernel15_0_r0_8_eq : ∀ k : Fin 16, kernel15_0Expr 0 8 k = kernel15_0_r0_8 k := by decide +kernel
lemma kernel15_0_r0_9_eq : ∀ k : Fin 16, kernel15_0Expr 0 9 k = kernel15_0_r0_9 k := by decide +kernel
lemma kernel15_0_r0_10_eq : ∀ k : Fin 16, kernel15_0Expr 0 10 k = kernel15_0_r0_10 k := by decide +kernel
lemma kernel15_0_r0_11_eq : ∀ k : Fin 16, kernel15_0Expr 0 11 k = kernel15_0_r0_11 k := by decide +kernel
lemma kernel15_0_r0_12_eq : ∀ k : Fin 16, kernel15_0Expr 0 12 k = kernel15_0_r0_12 k := by decide +kernel
lemma kernel15_0_r0_13_eq : ∀ k : Fin 16, kernel15_0Expr 0 13 k = kernel15_0_r0_13 k := by decide +kernel
lemma kernel15_0_r0_14_eq : ∀ k : Fin 16, kernel15_0Expr 0 14 k = kernel15_0_r0_14 k := by decide +kernel
lemma kernel15_0_r0_15_eq : ∀ k : Fin 16, kernel15_0Expr 0 15 k = kernel15_0_r0_15 k := by decide +kernel
lemma kernel15_0_r0_eq (i k : Fin 16) : kernel15_0Expr 0 i k = kernel15_0_r0 i k := by
  fin_cases i
  · exact kernel15_0_r0_0_eq k
  · exact kernel15_0_r0_1_eq k
  · exact kernel15_0_r0_2_eq k
  · exact kernel15_0_r0_3_eq k
  · exact kernel15_0_r0_4_eq k
  · exact kernel15_0_r0_5_eq k
  · exact kernel15_0_r0_6_eq k
  · exact kernel15_0_r0_7_eq k
  · exact kernel15_0_r0_8_eq k
  · exact kernel15_0_r0_9_eq k
  · exact kernel15_0_r0_10_eq k
  · exact kernel15_0_r0_11_eq k
  · exact kernel15_0_r0_12_eq k
  · exact kernel15_0_r0_13_eq k
  · exact kernel15_0_r0_14_eq k
  · exact kernel15_0_r0_15_eq k
lemma kernel15_0_r1_0_eq : ∀ k : Fin 16, kernel15_0Expr 1 0 k = kernel15_0_r1_0 k := by decide +kernel
lemma kernel15_0_r1_1_eq : ∀ k : Fin 16, kernel15_0Expr 1 1 k = kernel15_0_r1_1 k := by decide +kernel
lemma kernel15_0_r1_2_eq : ∀ k : Fin 16, kernel15_0Expr 1 2 k = kernel15_0_r1_2 k := by decide +kernel
lemma kernel15_0_r1_3_eq : ∀ k : Fin 16, kernel15_0Expr 1 3 k = kernel15_0_r1_3 k := by decide +kernel
lemma kernel15_0_r1_4_eq : ∀ k : Fin 16, kernel15_0Expr 1 4 k = kernel15_0_r1_4 k := by decide +kernel
lemma kernel15_0_r1_5_eq : ∀ k : Fin 16, kernel15_0Expr 1 5 k = kernel15_0_r1_5 k := by decide +kernel
lemma kernel15_0_r1_6_eq : ∀ k : Fin 16, kernel15_0Expr 1 6 k = kernel15_0_r1_6 k := by decide +kernel
lemma kernel15_0_r1_7_eq : ∀ k : Fin 16, kernel15_0Expr 1 7 k = kernel15_0_r1_7 k := by decide +kernel
lemma kernel15_0_r1_8_eq : ∀ k : Fin 16, kernel15_0Expr 1 8 k = kernel15_0_r1_8 k := by decide +kernel
lemma kernel15_0_r1_9_eq : ∀ k : Fin 16, kernel15_0Expr 1 9 k = kernel15_0_r1_9 k := by decide +kernel
lemma kernel15_0_r1_10_eq : ∀ k : Fin 16, kernel15_0Expr 1 10 k = kernel15_0_r1_10 k := by decide +kernel
lemma kernel15_0_r1_11_eq : ∀ k : Fin 16, kernel15_0Expr 1 11 k = kernel15_0_r1_11 k := by decide +kernel
lemma kernel15_0_r1_12_eq : ∀ k : Fin 16, kernel15_0Expr 1 12 k = kernel15_0_r1_12 k := by decide +kernel
lemma kernel15_0_r1_13_eq : ∀ k : Fin 16, kernel15_0Expr 1 13 k = kernel15_0_r1_13 k := by decide +kernel
lemma kernel15_0_r1_14_eq : ∀ k : Fin 16, kernel15_0Expr 1 14 k = kernel15_0_r1_14 k := by decide +kernel
lemma kernel15_0_r1_15_eq : ∀ k : Fin 16, kernel15_0Expr 1 15 k = kernel15_0_r1_15 k := by decide +kernel
lemma kernel15_0_r1_eq (i k : Fin 16) : kernel15_0Expr 1 i k = kernel15_0_r1 i k := by
  fin_cases i
  · exact kernel15_0_r1_0_eq k
  · exact kernel15_0_r1_1_eq k
  · exact kernel15_0_r1_2_eq k
  · exact kernel15_0_r1_3_eq k
  · exact kernel15_0_r1_4_eq k
  · exact kernel15_0_r1_5_eq k
  · exact kernel15_0_r1_6_eq k
  · exact kernel15_0_r1_7_eq k
  · exact kernel15_0_r1_8_eq k
  · exact kernel15_0_r1_9_eq k
  · exact kernel15_0_r1_10_eq k
  · exact kernel15_0_r1_11_eq k
  · exact kernel15_0_r1_12_eq k
  · exact kernel15_0_r1_13_eq k
  · exact kernel15_0_r1_14_eq k
  · exact kernel15_0_r1_15_eq k
lemma kernel15_0_eq_g_oai (j : Fin 6) (i k : Fin 16) : kernel15_0Expr j i k = kernel15_0 j i k := by
  fin_cases j
  · exact kernel15_0_r0_eq i k
  · exact kernel15_0_r1_eq i k
  · exact kernel15_0_r2_eq_g i k
  · exact kernel15_0_r3_eq_g i k
  · exact kernel15_0_r4_eq_g i k
  · exact kernel15_0_r5_eq_g i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.kernel15_0_eq_g_oai := @OAI.SharpPlanar.CachedData.kernel15_0_eq_g_oai
