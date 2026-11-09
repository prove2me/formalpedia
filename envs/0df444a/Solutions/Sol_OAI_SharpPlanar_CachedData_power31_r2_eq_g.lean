-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.power31_r2_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:46:44.59147+00:00
-- url     : https://prove2.me/submissions/d11ce385-1763-4709-a2b2-db51c9affa58

import Mathlib
import Definitions.Def_OAIQ098G251
import Definitions.Def_OAIQ098G319

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
lemma power31_r2_0_eq : ∀ k : Fin 16, power31Expr 2 0 k = power31_r2_0 k := by decide +kernel
lemma power31_r2_1_eq : ∀ k : Fin 16, power31Expr 2 1 k = power31_r2_1 k := by decide +kernel
lemma power31_r2_2_eq : ∀ k : Fin 16, power31Expr 2 2 k = power31_r2_2 k := by decide +kernel
lemma power31_r2_3_eq : ∀ k : Fin 16, power31Expr 2 3 k = power31_r2_3 k := by decide +kernel
lemma power31_r2_4_eq : ∀ k : Fin 16, power31Expr 2 4 k = power31_r2_4 k := by decide +kernel
lemma power31_r2_5_eq : ∀ k : Fin 16, power31Expr 2 5 k = power31_r2_5 k := by decide +kernel
lemma power31_r2_6_eq : ∀ k : Fin 16, power31Expr 2 6 k = power31_r2_6 k := by decide +kernel
lemma power31_r2_7_eq : ∀ k : Fin 16, power31Expr 2 7 k = power31_r2_7 k := by decide +kernel
lemma power31_r2_8_eq : ∀ k : Fin 16, power31Expr 2 8 k = power31_r2_8 k := by decide +kernel
lemma power31_r2_9_eq : ∀ k : Fin 16, power31Expr 2 9 k = power31_r2_9 k := by decide +kernel
lemma power31_r2_10_eq : ∀ k : Fin 16, power31Expr 2 10 k = power31_r2_10 k := by decide +kernel
lemma power31_r2_11_eq : ∀ k : Fin 16, power31Expr 2 11 k = power31_r2_11 k := by decide +kernel
lemma power31_r2_12_eq : ∀ k : Fin 16, power31Expr 2 12 k = power31_r2_12 k := by decide +kernel
lemma power31_r2_13_eq : ∀ k : Fin 16, power31Expr 2 13 k = power31_r2_13 k := by decide +kernel
lemma power31_r2_14_eq : ∀ k : Fin 16, power31Expr 2 14 k = power31_r2_14 k := by decide +kernel
lemma power31_r2_15_eq : ∀ k : Fin 16, power31Expr 2 15 k = power31_r2_15 k := by decide +kernel
lemma power31_r2_eq_g_oai (i k : Fin 16) : power31Expr 2 i k = power31_r2 i k := by
  fin_cases i
  · exact power31_r2_0_eq k
  · exact power31_r2_1_eq k
  · exact power31_r2_2_eq k
  · exact power31_r2_3_eq k
  · exact power31_r2_4_eq k
  · exact power31_r2_5_eq k
  · exact power31_r2_6_eq k
  · exact power31_r2_7_eq k
  · exact power31_r2_8_eq k
  · exact power31_r2_9_eq k
  · exact power31_r2_10_eq k
  · exact power31_r2_11_eq k
  · exact power31_r2_12_eq k
  · exact power31_r2_13_eq k
  · exact power31_r2_14_eq k
  · exact power31_r2_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.power31_r2_eq_g_oai := @OAI.SharpPlanar.CachedData.power31_r2_eq_g_oai
