-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.mpower1_3_r0_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:13:35.746679+00:00
-- url     : https://prove2.me/submissions/af32d1ca-a036-4999-99db-d4fd64070494

import Mathlib
import Definitions.Def_OAIQ098G462
import Definitions.Def_OAIQ098G1481

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
lemma mpower1_3_r0_0_eq : ∀ k : Fin 16, mpower1_3Expr 0 0 k = mpower1_3_r0_0 k := by decide +kernel
lemma mpower1_3_r0_1_eq : ∀ k : Fin 16, mpower1_3Expr 0 1 k = mpower1_3_r0_1 k := by decide +kernel
lemma mpower1_3_r0_2_eq : ∀ k : Fin 16, mpower1_3Expr 0 2 k = mpower1_3_r0_2 k := by decide +kernel
lemma mpower1_3_r0_3_eq : ∀ k : Fin 16, mpower1_3Expr 0 3 k = mpower1_3_r0_3 k := by decide +kernel
lemma mpower1_3_r0_4_eq : ∀ k : Fin 16, mpower1_3Expr 0 4 k = mpower1_3_r0_4 k := by decide +kernel
lemma mpower1_3_r0_5_eq : ∀ k : Fin 16, mpower1_3Expr 0 5 k = mpower1_3_r0_5 k := by decide +kernel
lemma mpower1_3_r0_6_eq : ∀ k : Fin 16, mpower1_3Expr 0 6 k = mpower1_3_r0_6 k := by decide +kernel
lemma mpower1_3_r0_7_eq : ∀ k : Fin 16, mpower1_3Expr 0 7 k = mpower1_3_r0_7 k := by decide +kernel
lemma mpower1_3_r0_8_eq : ∀ k : Fin 16, mpower1_3Expr 0 8 k = mpower1_3_r0_8 k := by decide +kernel
lemma mpower1_3_r0_9_eq : ∀ k : Fin 16, mpower1_3Expr 0 9 k = mpower1_3_r0_9 k := by decide +kernel
lemma mpower1_3_r0_10_eq : ∀ k : Fin 16, mpower1_3Expr 0 10 k = mpower1_3_r0_10 k := by decide +kernel
lemma mpower1_3_r0_11_eq : ∀ k : Fin 16, mpower1_3Expr 0 11 k = mpower1_3_r0_11 k := by decide +kernel
lemma mpower1_3_r0_12_eq : ∀ k : Fin 16, mpower1_3Expr 0 12 k = mpower1_3_r0_12 k := by decide +kernel
lemma mpower1_3_r0_13_eq : ∀ k : Fin 16, mpower1_3Expr 0 13 k = mpower1_3_r0_13 k := by decide +kernel
lemma mpower1_3_r0_14_eq : ∀ k : Fin 16, mpower1_3Expr 0 14 k = mpower1_3_r0_14 k := by decide +kernel
lemma mpower1_3_r0_15_eq : ∀ k : Fin 16, mpower1_3Expr 0 15 k = mpower1_3_r0_15 k := by decide +kernel
lemma mpower1_3_r0_eq_g_oai (i k : Fin 16) : mpower1_3Expr 0 i k = mpower1_3_r0 i k := by
  fin_cases i
  · exact mpower1_3_r0_0_eq k
  · exact mpower1_3_r0_1_eq k
  · exact mpower1_3_r0_2_eq k
  · exact mpower1_3_r0_3_eq k
  · exact mpower1_3_r0_4_eq k
  · exact mpower1_3_r0_5_eq k
  · exact mpower1_3_r0_6_eq k
  · exact mpower1_3_r0_7_eq k
  · exact mpower1_3_r0_8_eq k
  · exact mpower1_3_r0_9_eq k
  · exact mpower1_3_r0_10_eq k
  · exact mpower1_3_r0_11_eq k
  · exact mpower1_3_r0_12_eq k
  · exact mpower1_3_r0_13_eq k
  · exact mpower1_3_r0_14_eq k
  · exact mpower1_3_r0_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.mpower1_3_r0_eq_g_oai := @OAI.SharpPlanar.CachedData.mpower1_3_r0_eq_g_oai
