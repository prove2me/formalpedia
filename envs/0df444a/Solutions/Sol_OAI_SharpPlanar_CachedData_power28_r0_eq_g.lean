-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.power28_r0_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:14:55.217984+00:00
-- url     : https://prove2.me/submissions/1c7dc633-9c7d-47fb-a2b0-2469727f427c

import Mathlib
import Definitions.Def_OAIQ098G248

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers30
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
lemma power28_r0_0_eq : ∀ k : Fin 16, power28Expr 0 0 k = power28_r0_0 k := by decide +kernel
lemma power28_r0_1_eq : ∀ k : Fin 16, power28Expr 0 1 k = power28_r0_1 k := by decide +kernel
lemma power28_r0_2_eq : ∀ k : Fin 16, power28Expr 0 2 k = power28_r0_2 k := by decide +kernel
lemma power28_r0_3_eq : ∀ k : Fin 16, power28Expr 0 3 k = power28_r0_3 k := by decide +kernel
lemma power28_r0_4_eq : ∀ k : Fin 16, power28Expr 0 4 k = power28_r0_4 k := by decide +kernel
lemma power28_r0_5_eq : ∀ k : Fin 16, power28Expr 0 5 k = power28_r0_5 k := by decide +kernel
lemma power28_r0_6_eq : ∀ k : Fin 16, power28Expr 0 6 k = power28_r0_6 k := by decide +kernel
lemma power28_r0_7_eq : ∀ k : Fin 16, power28Expr 0 7 k = power28_r0_7 k := by decide +kernel
lemma power28_r0_8_eq : ∀ k : Fin 16, power28Expr 0 8 k = power28_r0_8 k := by decide +kernel
lemma power28_r0_9_eq : ∀ k : Fin 16, power28Expr 0 9 k = power28_r0_9 k := by decide +kernel
lemma power28_r0_10_eq : ∀ k : Fin 16, power28Expr 0 10 k = power28_r0_10 k := by decide +kernel
lemma power28_r0_11_eq : ∀ k : Fin 16, power28Expr 0 11 k = power28_r0_11 k := by decide +kernel
lemma power28_r0_12_eq : ∀ k : Fin 16, power28Expr 0 12 k = power28_r0_12 k := by decide +kernel
lemma power28_r0_13_eq : ∀ k : Fin 16, power28Expr 0 13 k = power28_r0_13 k := by decide +kernel
lemma power28_r0_14_eq : ∀ k : Fin 16, power28Expr 0 14 k = power28_r0_14 k := by decide +kernel
lemma power28_r0_15_eq : ∀ k : Fin 16, power28Expr 0 15 k = power28_r0_15 k := by decide +kernel
lemma power28_r0_eq_g_oai (i k : Fin 16) : power28Expr 0 i k = power28_r0 i k := by
  fin_cases i
  · exact power28_r0_0_eq k
  · exact power28_r0_1_eq k
  · exact power28_r0_2_eq k
  · exact power28_r0_3_eq k
  · exact power28_r0_4_eq k
  · exact power28_r0_5_eq k
  · exact power28_r0_6_eq k
  · exact power28_r0_7_eq k
  · exact power28_r0_8_eq k
  · exact power28_r0_9_eq k
  · exact power28_r0_10_eq k
  · exact power28_r0_11_eq k
  · exact power28_r0_12_eq k
  · exact power28_r0_13_eq k
  · exact power28_r0_14_eq k
  · exact power28_r0_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.power28_r0_eq_g_oai := @OAI.SharpPlanar.CachedData.power28_r0_eq_g_oai
