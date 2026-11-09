-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.kernel75_1_r5_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:07:28.873134+00:00
-- url     : https://prove2.me/submissions/b0d9371e-5fc0-47dc-b440-5172424487bb

import Mathlib
import Definitions.Def_OAIQ098G1445

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues80
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
lemma kernel75_1_r5_0_eq : ∀ k : Fin 16, kernel75_1Expr 5 0 k = kernel75_1_r5_0 k := by decide +kernel
lemma kernel75_1_r5_1_eq : ∀ k : Fin 16, kernel75_1Expr 5 1 k = kernel75_1_r5_1 k := by decide +kernel
lemma kernel75_1_r5_2_eq : ∀ k : Fin 16, kernel75_1Expr 5 2 k = kernel75_1_r5_2 k := by decide +kernel
lemma kernel75_1_r5_3_eq : ∀ k : Fin 16, kernel75_1Expr 5 3 k = kernel75_1_r5_3 k := by decide +kernel
lemma kernel75_1_r5_4_eq : ∀ k : Fin 16, kernel75_1Expr 5 4 k = kernel75_1_r5_4 k := by decide +kernel
lemma kernel75_1_r5_5_eq : ∀ k : Fin 16, kernel75_1Expr 5 5 k = kernel75_1_r5_5 k := by decide +kernel
lemma kernel75_1_r5_6_eq : ∀ k : Fin 16, kernel75_1Expr 5 6 k = kernel75_1_r5_6 k := by decide +kernel
lemma kernel75_1_r5_7_eq : ∀ k : Fin 16, kernel75_1Expr 5 7 k = kernel75_1_r5_7 k := by decide +kernel
lemma kernel75_1_r5_8_eq : ∀ k : Fin 16, kernel75_1Expr 5 8 k = kernel75_1_r5_8 k := by decide +kernel
lemma kernel75_1_r5_9_eq : ∀ k : Fin 16, kernel75_1Expr 5 9 k = kernel75_1_r5_9 k := by decide +kernel
lemma kernel75_1_r5_10_eq : ∀ k : Fin 16, kernel75_1Expr 5 10 k = kernel75_1_r5_10 k := by decide +kernel
lemma kernel75_1_r5_11_eq : ∀ k : Fin 16, kernel75_1Expr 5 11 k = kernel75_1_r5_11 k := by decide +kernel
lemma kernel75_1_r5_12_eq : ∀ k : Fin 16, kernel75_1Expr 5 12 k = kernel75_1_r5_12 k := by decide +kernel
lemma kernel75_1_r5_13_eq : ∀ k : Fin 16, kernel75_1Expr 5 13 k = kernel75_1_r5_13 k := by decide +kernel
lemma kernel75_1_r5_14_eq : ∀ k : Fin 16, kernel75_1Expr 5 14 k = kernel75_1_r5_14 k := by decide +kernel
lemma kernel75_1_r5_15_eq : ∀ k : Fin 16, kernel75_1Expr 5 15 k = kernel75_1_r5_15 k := by decide +kernel
lemma kernel75_1_r5_eq_g_oai (i k : Fin 16) : kernel75_1Expr 5 i k = kernel75_1_r5 i k := by
  fin_cases i
  · exact kernel75_1_r5_0_eq k
  · exact kernel75_1_r5_1_eq k
  · exact kernel75_1_r5_2_eq k
  · exact kernel75_1_r5_3_eq k
  · exact kernel75_1_r5_4_eq k
  · exact kernel75_1_r5_5_eq k
  · exact kernel75_1_r5_6_eq k
  · exact kernel75_1_r5_7_eq k
  · exact kernel75_1_r5_8_eq k
  · exact kernel75_1_r5_9_eq k
  · exact kernel75_1_r5_10_eq k
  · exact kernel75_1_r5_11_eq k
  · exact kernel75_1_r5_12_eq k
  · exact kernel75_1_r5_13_eq k
  · exact kernel75_1_r5_14_eq k
  · exact kernel75_1_r5_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.kernel75_1_r5_eq_g_oai := @OAI.SharpPlanar.CachedData.kernel75_1_r5_eq_g_oai
