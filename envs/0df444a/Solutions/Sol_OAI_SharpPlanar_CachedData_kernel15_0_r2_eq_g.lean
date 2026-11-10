-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.kernel15_0_r2_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T06:15:11.823743+00:00
-- url     : https://prove2.me/submissions/f25a4bc5-d908-435c-8925-2f4a1faa35de

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
lemma kernel15_0_r2_0_eq : ∀ k : Fin 16, kernel15_0Expr 2 0 k = kernel15_0_r2_0 k := by decide +kernel
lemma kernel15_0_r2_1_eq : ∀ k : Fin 16, kernel15_0Expr 2 1 k = kernel15_0_r2_1 k := by decide +kernel
lemma kernel15_0_r2_2_eq : ∀ k : Fin 16, kernel15_0Expr 2 2 k = kernel15_0_r2_2 k := by decide +kernel
lemma kernel15_0_r2_3_eq : ∀ k : Fin 16, kernel15_0Expr 2 3 k = kernel15_0_r2_3 k := by decide +kernel
lemma kernel15_0_r2_4_eq : ∀ k : Fin 16, kernel15_0Expr 2 4 k = kernel15_0_r2_4 k := by decide +kernel
lemma kernel15_0_r2_5_eq : ∀ k : Fin 16, kernel15_0Expr 2 5 k = kernel15_0_r2_5 k := by decide +kernel
lemma kernel15_0_r2_6_eq : ∀ k : Fin 16, kernel15_0Expr 2 6 k = kernel15_0_r2_6 k := by decide +kernel
lemma kernel15_0_r2_7_eq : ∀ k : Fin 16, kernel15_0Expr 2 7 k = kernel15_0_r2_7 k := by decide +kernel
lemma kernel15_0_r2_8_eq : ∀ k : Fin 16, kernel15_0Expr 2 8 k = kernel15_0_r2_8 k := by decide +kernel
lemma kernel15_0_r2_9_eq : ∀ k : Fin 16, kernel15_0Expr 2 9 k = kernel15_0_r2_9 k := by decide +kernel
lemma kernel15_0_r2_10_eq : ∀ k : Fin 16, kernel15_0Expr 2 10 k = kernel15_0_r2_10 k := by decide +kernel
lemma kernel15_0_r2_11_eq : ∀ k : Fin 16, kernel15_0Expr 2 11 k = kernel15_0_r2_11 k := by decide +kernel
lemma kernel15_0_r2_12_eq : ∀ k : Fin 16, kernel15_0Expr 2 12 k = kernel15_0_r2_12 k := by decide +kernel
lemma kernel15_0_r2_13_eq : ∀ k : Fin 16, kernel15_0Expr 2 13 k = kernel15_0_r2_13 k := by decide +kernel
lemma kernel15_0_r2_14_eq : ∀ k : Fin 16, kernel15_0Expr 2 14 k = kernel15_0_r2_14 k := by decide +kernel
lemma kernel15_0_r2_15_eq : ∀ k : Fin 16, kernel15_0Expr 2 15 k = kernel15_0_r2_15 k := by decide +kernel
lemma kernel15_0_r2_eq_g_oai (i k : Fin 16) : kernel15_0Expr 2 i k = kernel15_0_r2 i k := by
  fin_cases i
  · exact kernel15_0_r2_0_eq k
  · exact kernel15_0_r2_1_eq k
  · exact kernel15_0_r2_2_eq k
  · exact kernel15_0_r2_3_eq k
  · exact kernel15_0_r2_4_eq k
  · exact kernel15_0_r2_5_eq k
  · exact kernel15_0_r2_6_eq k
  · exact kernel15_0_r2_7_eq k
  · exact kernel15_0_r2_8_eq k
  · exact kernel15_0_r2_9_eq k
  · exact kernel15_0_r2_10_eq k
  · exact kernel15_0_r2_11_eq k
  · exact kernel15_0_r2_12_eq k
  · exact kernel15_0_r2_13_eq k
  · exact kernel15_0_r2_14_eq k
  · exact kernel15_0_r2_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.kernel15_0_r2_eq_g_oai := @OAI.SharpPlanar.CachedData.kernel15_0_r2_eq_g_oai
