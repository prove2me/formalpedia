-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.mpower0_22_r4_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:10:36.042637+00:00
-- url     : https://prove2.me/submissions/ad7a61e7-5060-4b78-9b58-0be49a045362

import Mathlib
import Definitions.Def_OAIQ098G1466

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers25
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
open IntegerIntervals IntegerBasis IntegerGrid
lemma mpower0_22_r4_0_eq : ∀ k : Fin 16, mpower0_22Expr 4 0 k = mpower0_22_r4_0 k := by decide +kernel
lemma mpower0_22_r4_1_eq : ∀ k : Fin 16, mpower0_22Expr 4 1 k = mpower0_22_r4_1 k := by decide +kernel
lemma mpower0_22_r4_2_eq : ∀ k : Fin 16, mpower0_22Expr 4 2 k = mpower0_22_r4_2 k := by decide +kernel
lemma mpower0_22_r4_3_eq : ∀ k : Fin 16, mpower0_22Expr 4 3 k = mpower0_22_r4_3 k := by decide +kernel
lemma mpower0_22_r4_4_eq : ∀ k : Fin 16, mpower0_22Expr 4 4 k = mpower0_22_r4_4 k := by decide +kernel
lemma mpower0_22_r4_5_eq : ∀ k : Fin 16, mpower0_22Expr 4 5 k = mpower0_22_r4_5 k := by decide +kernel
lemma mpower0_22_r4_6_eq : ∀ k : Fin 16, mpower0_22Expr 4 6 k = mpower0_22_r4_6 k := by decide +kernel
lemma mpower0_22_r4_7_eq : ∀ k : Fin 16, mpower0_22Expr 4 7 k = mpower0_22_r4_7 k := by decide +kernel
lemma mpower0_22_r4_8_eq : ∀ k : Fin 16, mpower0_22Expr 4 8 k = mpower0_22_r4_8 k := by decide +kernel
lemma mpower0_22_r4_9_eq : ∀ k : Fin 16, mpower0_22Expr 4 9 k = mpower0_22_r4_9 k := by decide +kernel
lemma mpower0_22_r4_10_eq : ∀ k : Fin 16, mpower0_22Expr 4 10 k = mpower0_22_r4_10 k := by decide +kernel
lemma mpower0_22_r4_11_eq : ∀ k : Fin 16, mpower0_22Expr 4 11 k = mpower0_22_r4_11 k := by decide +kernel
lemma mpower0_22_r4_12_eq : ∀ k : Fin 16, mpower0_22Expr 4 12 k = mpower0_22_r4_12 k := by decide +kernel
lemma mpower0_22_r4_13_eq : ∀ k : Fin 16, mpower0_22Expr 4 13 k = mpower0_22_r4_13 k := by decide +kernel
lemma mpower0_22_r4_14_eq : ∀ k : Fin 16, mpower0_22Expr 4 14 k = mpower0_22_r4_14 k := by decide +kernel
lemma mpower0_22_r4_15_eq : ∀ k : Fin 16, mpower0_22Expr 4 15 k = mpower0_22_r4_15 k := by decide +kernel
lemma mpower0_22_r4_eq_g_oai (i k : Fin 16) : mpower0_22Expr 4 i k = mpower0_22_r4 i k := by
  fin_cases i
  · exact mpower0_22_r4_0_eq k
  · exact mpower0_22_r4_1_eq k
  · exact mpower0_22_r4_2_eq k
  · exact mpower0_22_r4_3_eq k
  · exact mpower0_22_r4_4_eq k
  · exact mpower0_22_r4_5_eq k
  · exact mpower0_22_r4_6_eq k
  · exact mpower0_22_r4_7_eq k
  · exact mpower0_22_r4_8_eq k
  · exact mpower0_22_r4_9_eq k
  · exact mpower0_22_r4_10_eq k
  · exact mpower0_22_r4_11_eq k
  · exact mpower0_22_r4_12_eq k
  · exact mpower0_22_r4_13_eq k
  · exact mpower0_22_r4_14_eq k
  · exact mpower0_22_r4_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.mpower0_22_r4_eq_g_oai := @OAI.SharpPlanar.CachedData.mpower0_22_r4_eq_g_oai
