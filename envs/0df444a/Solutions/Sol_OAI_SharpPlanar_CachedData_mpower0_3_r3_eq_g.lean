-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.mpower0_3_r3_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:11:13.69304+00:00
-- url     : https://prove2.me/submissions/78568530-bc85-4a6d-b6d6-6a22df914c42

import Mathlib
import Definitions.Def_OAIQ098G431
import Definitions.Def_OAIQ098G1464

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers5
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
lemma mpower0_3_r3_0_eq : ∀ k : Fin 16, mpower0_3Expr 3 0 k = mpower0_3_r3_0 k := by decide +kernel
lemma mpower0_3_r3_1_eq : ∀ k : Fin 16, mpower0_3Expr 3 1 k = mpower0_3_r3_1 k := by decide +kernel
lemma mpower0_3_r3_2_eq : ∀ k : Fin 16, mpower0_3Expr 3 2 k = mpower0_3_r3_2 k := by decide +kernel
lemma mpower0_3_r3_3_eq : ∀ k : Fin 16, mpower0_3Expr 3 3 k = mpower0_3_r3_3 k := by decide +kernel
lemma mpower0_3_r3_4_eq : ∀ k : Fin 16, mpower0_3Expr 3 4 k = mpower0_3_r3_4 k := by decide +kernel
lemma mpower0_3_r3_5_eq : ∀ k : Fin 16, mpower0_3Expr 3 5 k = mpower0_3_r3_5 k := by decide +kernel
lemma mpower0_3_r3_6_eq : ∀ k : Fin 16, mpower0_3Expr 3 6 k = mpower0_3_r3_6 k := by decide +kernel
lemma mpower0_3_r3_7_eq : ∀ k : Fin 16, mpower0_3Expr 3 7 k = mpower0_3_r3_7 k := by decide +kernel
lemma mpower0_3_r3_8_eq : ∀ k : Fin 16, mpower0_3Expr 3 8 k = mpower0_3_r3_8 k := by decide +kernel
lemma mpower0_3_r3_9_eq : ∀ k : Fin 16, mpower0_3Expr 3 9 k = mpower0_3_r3_9 k := by decide +kernel
lemma mpower0_3_r3_10_eq : ∀ k : Fin 16, mpower0_3Expr 3 10 k = mpower0_3_r3_10 k := by decide +kernel
lemma mpower0_3_r3_11_eq : ∀ k : Fin 16, mpower0_3Expr 3 11 k = mpower0_3_r3_11 k := by decide +kernel
lemma mpower0_3_r3_12_eq : ∀ k : Fin 16, mpower0_3Expr 3 12 k = mpower0_3_r3_12 k := by decide +kernel
lemma mpower0_3_r3_13_eq : ∀ k : Fin 16, mpower0_3Expr 3 13 k = mpower0_3_r3_13 k := by decide +kernel
lemma mpower0_3_r3_14_eq : ∀ k : Fin 16, mpower0_3Expr 3 14 k = mpower0_3_r3_14 k := by decide +kernel
lemma mpower0_3_r3_15_eq : ∀ k : Fin 16, mpower0_3Expr 3 15 k = mpower0_3_r3_15 k := by decide +kernel
lemma mpower0_3_r3_eq_g_oai (i k : Fin 16) : mpower0_3Expr 3 i k = mpower0_3_r3 i k := by
  fin_cases i
  · exact mpower0_3_r3_0_eq k
  · exact mpower0_3_r3_1_eq k
  · exact mpower0_3_r3_2_eq k
  · exact mpower0_3_r3_3_eq k
  · exact mpower0_3_r3_4_eq k
  · exact mpower0_3_r3_5_eq k
  · exact mpower0_3_r3_6_eq k
  · exact mpower0_3_r3_7_eq k
  · exact mpower0_3_r3_8_eq k
  · exact mpower0_3_r3_9_eq k
  · exact mpower0_3_r3_10_eq k
  · exact mpower0_3_r3_11_eq k
  · exact mpower0_3_r3_12_eq k
  · exact mpower0_3_r3_13_eq k
  · exact mpower0_3_r3_14_eq k
  · exact mpower0_3_r3_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.mpower0_3_r3_eq_g_oai := @OAI.SharpPlanar.CachedData.mpower0_3_r3_eq_g_oai
