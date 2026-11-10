-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.amp0_10_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T08:20:59.873085+00:00
-- url     : https://prove2.me/submissions/c746d8b0-bfa5-4d06-ac46-e4fff0e46386

import Mathlib
import Definitions.Def_OAIQ098G103

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Amplitudes
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
lemma amp0_10_0_eq : ∀ k : Fin 16, amp0_1Expr 0 0 k = amp0_10_0 k := by decide +kernel
lemma amp0_10_1_eq : ∀ k : Fin 16, amp0_1Expr 0 1 k = amp0_10_1 k := by decide +kernel
lemma amp0_10_2_eq : ∀ k : Fin 16, amp0_1Expr 0 2 k = amp0_10_2 k := by decide +kernel
lemma amp0_10_3_eq : ∀ k : Fin 16, amp0_1Expr 0 3 k = amp0_10_3 k := by decide +kernel
lemma amp0_10_4_eq : ∀ k : Fin 16, amp0_1Expr 0 4 k = amp0_10_4 k := by decide +kernel
lemma amp0_10_5_eq : ∀ k : Fin 16, amp0_1Expr 0 5 k = amp0_10_5 k := by decide +kernel
lemma amp0_10_6_eq : ∀ k : Fin 16, amp0_1Expr 0 6 k = amp0_10_6 k := by decide +kernel
lemma amp0_10_7_eq : ∀ k : Fin 16, amp0_1Expr 0 7 k = amp0_10_7 k := by decide +kernel
lemma amp0_10_8_eq : ∀ k : Fin 16, amp0_1Expr 0 8 k = amp0_10_8 k := by decide +kernel
lemma amp0_10_9_eq : ∀ k : Fin 16, amp0_1Expr 0 9 k = amp0_10_9 k := by decide +kernel
lemma amp0_10_10_eq : ∀ k : Fin 16, amp0_1Expr 0 10 k = amp0_10_10 k := by decide +kernel
lemma amp0_10_11_eq : ∀ k : Fin 16, amp0_1Expr 0 11 k = amp0_10_11 k := by decide +kernel
lemma amp0_10_12_eq : ∀ k : Fin 16, amp0_1Expr 0 12 k = amp0_10_12 k := by decide +kernel
lemma amp0_10_13_eq : ∀ k : Fin 16, amp0_1Expr 0 13 k = amp0_10_13 k := by decide +kernel
lemma amp0_10_14_eq : ∀ k : Fin 16, amp0_1Expr 0 14 k = amp0_10_14 k := by decide +kernel
lemma amp0_10_15_eq : ∀ k : Fin 16, amp0_1Expr 0 15 k = amp0_10_15 k := by decide +kernel
lemma amp0_10_eq_g_oai (i k : Fin 16) : amp0_1Expr 0 i k = amp0_10 i k := by
  fin_cases i
  · exact amp0_10_0_eq k
  · exact amp0_10_1_eq k
  · exact amp0_10_2_eq k
  · exact amp0_10_3_eq k
  · exact amp0_10_4_eq k
  · exact amp0_10_5_eq k
  · exact amp0_10_6_eq k
  · exact amp0_10_7_eq k
  · exact amp0_10_8_eq k
  · exact amp0_10_9_eq k
  · exact amp0_10_10_eq k
  · exact amp0_10_11_eq k
  · exact amp0_10_12_eq k
  · exact amp0_10_13_eq k
  · exact amp0_10_14_eq k
  · exact amp0_10_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.amp0_10_eq_g_oai := @OAI.SharpPlanar.CachedData.amp0_10_eq_g_oai
