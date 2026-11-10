-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.amp0_03_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T06:08:07.942589+00:00
-- url     : https://prove2.me/submissions/07752f05-d4e9-4854-81da-3914c8b62a55

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
lemma amp0_03_0_eq : ∀ k : Fin 16, amp0_0Expr 3 0 k = amp0_03_0 k := by decide +kernel
lemma amp0_03_1_eq : ∀ k : Fin 16, amp0_0Expr 3 1 k = amp0_03_1 k := by decide +kernel
lemma amp0_03_2_eq : ∀ k : Fin 16, amp0_0Expr 3 2 k = amp0_03_2 k := by decide +kernel
lemma amp0_03_3_eq : ∀ k : Fin 16, amp0_0Expr 3 3 k = amp0_03_3 k := by decide +kernel
lemma amp0_03_4_eq : ∀ k : Fin 16, amp0_0Expr 3 4 k = amp0_03_4 k := by decide +kernel
lemma amp0_03_5_eq : ∀ k : Fin 16, amp0_0Expr 3 5 k = amp0_03_5 k := by decide +kernel
lemma amp0_03_6_eq : ∀ k : Fin 16, amp0_0Expr 3 6 k = amp0_03_6 k := by decide +kernel
lemma amp0_03_7_eq : ∀ k : Fin 16, amp0_0Expr 3 7 k = amp0_03_7 k := by decide +kernel
lemma amp0_03_8_eq : ∀ k : Fin 16, amp0_0Expr 3 8 k = amp0_03_8 k := by decide +kernel
lemma amp0_03_9_eq : ∀ k : Fin 16, amp0_0Expr 3 9 k = amp0_03_9 k := by decide +kernel
lemma amp0_03_10_eq : ∀ k : Fin 16, amp0_0Expr 3 10 k = amp0_03_10 k := by decide +kernel
lemma amp0_03_11_eq : ∀ k : Fin 16, amp0_0Expr 3 11 k = amp0_03_11 k := by decide +kernel
lemma amp0_03_12_eq : ∀ k : Fin 16, amp0_0Expr 3 12 k = amp0_03_12 k := by decide +kernel
lemma amp0_03_13_eq : ∀ k : Fin 16, amp0_0Expr 3 13 k = amp0_03_13 k := by decide +kernel
lemma amp0_03_14_eq : ∀ k : Fin 16, amp0_0Expr 3 14 k = amp0_03_14 k := by decide +kernel
lemma amp0_03_15_eq : ∀ k : Fin 16, amp0_0Expr 3 15 k = amp0_03_15 k := by decide +kernel
lemma amp0_03_eq_g_oai (i k : Fin 16) : amp0_0Expr 3 i k = amp0_03 i k := by
  fin_cases i
  · exact amp0_03_0_eq k
  · exact amp0_03_1_eq k
  · exact amp0_03_2_eq k
  · exact amp0_03_3_eq k
  · exact amp0_03_4_eq k
  · exact amp0_03_5_eq k
  · exact amp0_03_6_eq k
  · exact amp0_03_7_eq k
  · exact amp0_03_8_eq k
  · exact amp0_03_9_eq k
  · exact amp0_03_10_eq k
  · exact amp0_03_11_eq k
  · exact amp0_03_12_eq k
  · exact amp0_03_13_eq k
  · exact amp0_03_14_eq k
  · exact amp0_03_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.amp0_03_eq_g_oai := @OAI.SharpPlanar.CachedData.amp0_03_eq_g_oai
