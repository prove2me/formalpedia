-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.amp4_12_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:08:12.391355+00:00
-- url     : https://prove2.me/submissions/3ac42ee4-8a2e-4143-a724-0d183ba12d43

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G021

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
lemma amp4_12_0_eq : ∀ k : Fin 16, amp4_1Expr 2 0 k = amp4_12_0 k := by decide +kernel
lemma amp4_12_1_eq : ∀ k : Fin 16, amp4_1Expr 2 1 k = amp4_12_1 k := by decide +kernel
lemma amp4_12_2_eq : ∀ k : Fin 16, amp4_1Expr 2 2 k = amp4_12_2 k := by decide +kernel
lemma amp4_12_3_eq : ∀ k : Fin 16, amp4_1Expr 2 3 k = amp4_12_3 k := by decide +kernel
lemma amp4_12_4_eq : ∀ k : Fin 16, amp4_1Expr 2 4 k = amp4_12_4 k := by decide +kernel
lemma amp4_12_5_eq : ∀ k : Fin 16, amp4_1Expr 2 5 k = amp4_12_5 k := by decide +kernel
lemma amp4_12_6_eq : ∀ k : Fin 16, amp4_1Expr 2 6 k = amp4_12_6 k := by decide +kernel
lemma amp4_12_7_eq : ∀ k : Fin 16, amp4_1Expr 2 7 k = amp4_12_7 k := by decide +kernel
lemma amp4_12_8_eq : ∀ k : Fin 16, amp4_1Expr 2 8 k = amp4_12_8 k := by decide +kernel
lemma amp4_12_9_eq : ∀ k : Fin 16, amp4_1Expr 2 9 k = amp4_12_9 k := by decide +kernel
lemma amp4_12_10_eq : ∀ k : Fin 16, amp4_1Expr 2 10 k = amp4_12_10 k := by decide +kernel
lemma amp4_12_11_eq : ∀ k : Fin 16, amp4_1Expr 2 11 k = amp4_12_11 k := by decide +kernel
lemma amp4_12_12_eq : ∀ k : Fin 16, amp4_1Expr 2 12 k = amp4_12_12 k := by decide +kernel
lemma amp4_12_13_eq : ∀ k : Fin 16, amp4_1Expr 2 13 k = amp4_12_13 k := by decide +kernel
lemma amp4_12_14_eq : ∀ k : Fin 16, amp4_1Expr 2 14 k = amp4_12_14 k := by decide +kernel
lemma amp4_12_15_eq : ∀ k : Fin 16, amp4_1Expr 2 15 k = amp4_12_15 k := by decide +kernel
lemma amp4_12_eq_g_oai (i k : Fin 16) : amp4_1Expr 2 i k = amp4_12 i k := by
  fin_cases i
  · exact amp4_12_0_eq k
  · exact amp4_12_1_eq k
  · exact amp4_12_2_eq k
  · exact amp4_12_3_eq k
  · exact amp4_12_4_eq k
  · exact amp4_12_5_eq k
  · exact amp4_12_6_eq k
  · exact amp4_12_7_eq k
  · exact amp4_12_8_eq k
  · exact amp4_12_9_eq k
  · exact amp4_12_10_eq k
  · exact amp4_12_11_eq k
  · exact amp4_12_12_eq k
  · exact amp4_12_13_eq k
  · exact amp4_12_14_eq k
  · exact amp4_12_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.amp4_12_eq_g_oai := @OAI.SharpPlanar.CachedData.amp4_12_eq_g_oai
