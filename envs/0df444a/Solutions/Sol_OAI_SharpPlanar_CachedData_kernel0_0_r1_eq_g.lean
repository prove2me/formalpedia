-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.kernel0_0_r1_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:03:49.307197+00:00
-- url     : https://prove2.me/submissions/ec6f7813-4a1a-4afc-a8ec-11f66456353c

import Mathlib
import Definitions.Def_OAIQ098G435
import Definitions.Def_OAIQ098G1405

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
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
lemma kernel0_0_r1_0_eq : ∀ k : Fin 16, kernel0_0Expr 1 0 k = kernel0_0_r1_0 k := by decide +kernel
lemma kernel0_0_r1_1_eq : ∀ k : Fin 16, kernel0_0Expr 1 1 k = kernel0_0_r1_1 k := by decide +kernel
lemma kernel0_0_r1_2_eq : ∀ k : Fin 16, kernel0_0Expr 1 2 k = kernel0_0_r1_2 k := by decide +kernel
lemma kernel0_0_r1_3_eq : ∀ k : Fin 16, kernel0_0Expr 1 3 k = kernel0_0_r1_3 k := by decide +kernel
lemma kernel0_0_r1_4_eq : ∀ k : Fin 16, kernel0_0Expr 1 4 k = kernel0_0_r1_4 k := by decide +kernel
lemma kernel0_0_r1_5_eq : ∀ k : Fin 16, kernel0_0Expr 1 5 k = kernel0_0_r1_5 k := by decide +kernel
lemma kernel0_0_r1_6_eq : ∀ k : Fin 16, kernel0_0Expr 1 6 k = kernel0_0_r1_6 k := by decide +kernel
lemma kernel0_0_r1_7_eq : ∀ k : Fin 16, kernel0_0Expr 1 7 k = kernel0_0_r1_7 k := by decide +kernel
lemma kernel0_0_r1_8_eq : ∀ k : Fin 16, kernel0_0Expr 1 8 k = kernel0_0_r1_8 k := by decide +kernel
lemma kernel0_0_r1_9_eq : ∀ k : Fin 16, kernel0_0Expr 1 9 k = kernel0_0_r1_9 k := by decide +kernel
lemma kernel0_0_r1_10_eq : ∀ k : Fin 16, kernel0_0Expr 1 10 k = kernel0_0_r1_10 k := by decide +kernel
lemma kernel0_0_r1_11_eq : ∀ k : Fin 16, kernel0_0Expr 1 11 k = kernel0_0_r1_11 k := by decide +kernel
lemma kernel0_0_r1_12_eq : ∀ k : Fin 16, kernel0_0Expr 1 12 k = kernel0_0_r1_12 k := by decide +kernel
lemma kernel0_0_r1_13_eq : ∀ k : Fin 16, kernel0_0Expr 1 13 k = kernel0_0_r1_13 k := by decide +kernel
lemma kernel0_0_r1_14_eq : ∀ k : Fin 16, kernel0_0Expr 1 14 k = kernel0_0_r1_14 k := by decide +kernel
lemma kernel0_0_r1_15_eq : ∀ k : Fin 16, kernel0_0Expr 1 15 k = kernel0_0_r1_15 k := by decide +kernel
lemma kernel0_0_r1_eq_g_oai (i k : Fin 16) : kernel0_0Expr 1 i k = kernel0_0_r1 i k := by
  fin_cases i
  · exact kernel0_0_r1_0_eq k
  · exact kernel0_0_r1_1_eq k
  · exact kernel0_0_r1_2_eq k
  · exact kernel0_0_r1_3_eq k
  · exact kernel0_0_r1_4_eq k
  · exact kernel0_0_r1_5_eq k
  · exact kernel0_0_r1_6_eq k
  · exact kernel0_0_r1_7_eq k
  · exact kernel0_0_r1_8_eq k
  · exact kernel0_0_r1_9_eq k
  · exact kernel0_0_r1_10_eq k
  · exact kernel0_0_r1_11_eq k
  · exact kernel0_0_r1_12_eq k
  · exact kernel0_0_r1_13_eq k
  · exact kernel0_0_r1_14_eq k
  · exact kernel0_0_r1_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.kernel0_0_r1_eq_g_oai := @OAI.SharpPlanar.CachedData.kernel0_0_r1_eq_g_oai
