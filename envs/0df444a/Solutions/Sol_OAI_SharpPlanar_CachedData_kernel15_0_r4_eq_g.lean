-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.kernel15_0_r4_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:22:06.863181+00:00
-- url     : https://prove2.me/submissions/e826b4c4-23f9-406f-a71a-39cc8bb3e6bb

import Mathlib
import Definitions.Def_OAIQ098G121
import Definitions.Def_OAIQ098G302

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
lemma kernel15_0_r4_0_eq : ∀ k : Fin 16, kernel15_0Expr 4 0 k = kernel15_0_r4_0 k := by decide +kernel
lemma kernel15_0_r4_1_eq : ∀ k : Fin 16, kernel15_0Expr 4 1 k = kernel15_0_r4_1 k := by decide +kernel
lemma kernel15_0_r4_2_eq : ∀ k : Fin 16, kernel15_0Expr 4 2 k = kernel15_0_r4_2 k := by decide +kernel
lemma kernel15_0_r4_3_eq : ∀ k : Fin 16, kernel15_0Expr 4 3 k = kernel15_0_r4_3 k := by decide +kernel
lemma kernel15_0_r4_4_eq : ∀ k : Fin 16, kernel15_0Expr 4 4 k = kernel15_0_r4_4 k := by decide +kernel
lemma kernel15_0_r4_5_eq : ∀ k : Fin 16, kernel15_0Expr 4 5 k = kernel15_0_r4_5 k := by decide +kernel
lemma kernel15_0_r4_6_eq : ∀ k : Fin 16, kernel15_0Expr 4 6 k = kernel15_0_r4_6 k := by decide +kernel
lemma kernel15_0_r4_7_eq : ∀ k : Fin 16, kernel15_0Expr 4 7 k = kernel15_0_r4_7 k := by decide +kernel
lemma kernel15_0_r4_8_eq : ∀ k : Fin 16, kernel15_0Expr 4 8 k = kernel15_0_r4_8 k := by decide +kernel
lemma kernel15_0_r4_9_eq : ∀ k : Fin 16, kernel15_0Expr 4 9 k = kernel15_0_r4_9 k := by decide +kernel
lemma kernel15_0_r4_10_eq : ∀ k : Fin 16, kernel15_0Expr 4 10 k = kernel15_0_r4_10 k := by decide +kernel
lemma kernel15_0_r4_11_eq : ∀ k : Fin 16, kernel15_0Expr 4 11 k = kernel15_0_r4_11 k := by decide +kernel
lemma kernel15_0_r4_12_eq : ∀ k : Fin 16, kernel15_0Expr 4 12 k = kernel15_0_r4_12 k := by decide +kernel
lemma kernel15_0_r4_13_eq : ∀ k : Fin 16, kernel15_0Expr 4 13 k = kernel15_0_r4_13 k := by decide +kernel
lemma kernel15_0_r4_14_eq : ∀ k : Fin 16, kernel15_0Expr 4 14 k = kernel15_0_r4_14 k := by decide +kernel
lemma kernel15_0_r4_15_eq : ∀ k : Fin 16, kernel15_0Expr 4 15 k = kernel15_0_r4_15 k := by decide +kernel
lemma kernel15_0_r4_eq_g_oai (i k : Fin 16) : kernel15_0Expr 4 i k = kernel15_0_r4 i k := by
  fin_cases i
  · exact kernel15_0_r4_0_eq k
  · exact kernel15_0_r4_1_eq k
  · exact kernel15_0_r4_2_eq k
  · exact kernel15_0_r4_3_eq k
  · exact kernel15_0_r4_4_eq k
  · exact kernel15_0_r4_5_eq k
  · exact kernel15_0_r4_6_eq k
  · exact kernel15_0_r4_7_eq k
  · exact kernel15_0_r4_8_eq k
  · exact kernel15_0_r4_9_eq k
  · exact kernel15_0_r4_10_eq k
  · exact kernel15_0_r4_11_eq k
  · exact kernel15_0_r4_12_eq k
  · exact kernel15_0_r4_13_eq k
  · exact kernel15_0_r4_14_eq k
  · exact kernel15_0_r4_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.kernel15_0_r4_eq_g_oai := @OAI.SharpPlanar.CachedData.kernel15_0_r4_eq_g_oai
