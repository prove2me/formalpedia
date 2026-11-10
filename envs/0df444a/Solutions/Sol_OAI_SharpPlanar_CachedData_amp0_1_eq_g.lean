-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.amp0_1_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T08:21:01.418423+00:00
-- url     : https://prove2.me/submissions/cb74e9a3-ee5a-44d8-b5c3-b2b9e68342ce

import Mathlib
import Definitions.Def_OAIQ098G103
import Theorems.Thm_OAI_SharpPlanar_CachedData_amp0_10_eq_g

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
lemma amp0_11_0_eq : ∀ k : Fin 16, amp0_1Expr 1 0 k = amp0_11_0 k := by decide +kernel
lemma amp0_11_1_eq : ∀ k : Fin 16, amp0_1Expr 1 1 k = amp0_11_1 k := by decide +kernel
lemma amp0_11_2_eq : ∀ k : Fin 16, amp0_1Expr 1 2 k = amp0_11_2 k := by decide +kernel
lemma amp0_11_3_eq : ∀ k : Fin 16, amp0_1Expr 1 3 k = amp0_11_3 k := by decide +kernel
lemma amp0_11_4_eq : ∀ k : Fin 16, amp0_1Expr 1 4 k = amp0_11_4 k := by decide +kernel
lemma amp0_11_5_eq : ∀ k : Fin 16, amp0_1Expr 1 5 k = amp0_11_5 k := by decide +kernel
lemma amp0_11_6_eq : ∀ k : Fin 16, amp0_1Expr 1 6 k = amp0_11_6 k := by decide +kernel
lemma amp0_11_7_eq : ∀ k : Fin 16, amp0_1Expr 1 7 k = amp0_11_7 k := by decide +kernel
lemma amp0_11_8_eq : ∀ k : Fin 16, amp0_1Expr 1 8 k = amp0_11_8 k := by decide +kernel
lemma amp0_11_9_eq : ∀ k : Fin 16, amp0_1Expr 1 9 k = amp0_11_9 k := by decide +kernel
lemma amp0_11_10_eq : ∀ k : Fin 16, amp0_1Expr 1 10 k = amp0_11_10 k := by decide +kernel
lemma amp0_11_11_eq : ∀ k : Fin 16, amp0_1Expr 1 11 k = amp0_11_11 k := by decide +kernel
lemma amp0_11_12_eq : ∀ k : Fin 16, amp0_1Expr 1 12 k = amp0_11_12 k := by decide +kernel
lemma amp0_11_13_eq : ∀ k : Fin 16, amp0_1Expr 1 13 k = amp0_11_13 k := by decide +kernel
lemma amp0_11_14_eq : ∀ k : Fin 16, amp0_1Expr 1 14 k = amp0_11_14 k := by decide +kernel
lemma amp0_11_15_eq : ∀ k : Fin 16, amp0_1Expr 1 15 k = amp0_11_15 k := by decide +kernel
lemma amp0_11_eq (i k : Fin 16) : amp0_1Expr 1 i k = amp0_11 i k := by
  fin_cases i
  · exact amp0_11_0_eq k
  · exact amp0_11_1_eq k
  · exact amp0_11_2_eq k
  · exact amp0_11_3_eq k
  · exact amp0_11_4_eq k
  · exact amp0_11_5_eq k
  · exact amp0_11_6_eq k
  · exact amp0_11_7_eq k
  · exact amp0_11_8_eq k
  · exact amp0_11_9_eq k
  · exact amp0_11_10_eq k
  · exact amp0_11_11_eq k
  · exact amp0_11_12_eq k
  · exact amp0_11_13_eq k
  · exact amp0_11_14_eq k
  · exact amp0_11_15_eq k
lemma amp0_12_0_eq : ∀ k : Fin 16, amp0_1Expr 2 0 k = amp0_12_0 k := by decide +kernel
lemma amp0_12_1_eq : ∀ k : Fin 16, amp0_1Expr 2 1 k = amp0_12_1 k := by decide +kernel
lemma amp0_12_2_eq : ∀ k : Fin 16, amp0_1Expr 2 2 k = amp0_12_2 k := by decide +kernel
lemma amp0_12_3_eq : ∀ k : Fin 16, amp0_1Expr 2 3 k = amp0_12_3 k := by decide +kernel
lemma amp0_12_4_eq : ∀ k : Fin 16, amp0_1Expr 2 4 k = amp0_12_4 k := by decide +kernel
lemma amp0_12_5_eq : ∀ k : Fin 16, amp0_1Expr 2 5 k = amp0_12_5 k := by decide +kernel
lemma amp0_12_6_eq : ∀ k : Fin 16, amp0_1Expr 2 6 k = amp0_12_6 k := by decide +kernel
lemma amp0_12_7_eq : ∀ k : Fin 16, amp0_1Expr 2 7 k = amp0_12_7 k := by decide +kernel
lemma amp0_12_8_eq : ∀ k : Fin 16, amp0_1Expr 2 8 k = amp0_12_8 k := by decide +kernel
lemma amp0_12_9_eq : ∀ k : Fin 16, amp0_1Expr 2 9 k = amp0_12_9 k := by decide +kernel
lemma amp0_12_10_eq : ∀ k : Fin 16, amp0_1Expr 2 10 k = amp0_12_10 k := by decide +kernel
lemma amp0_12_11_eq : ∀ k : Fin 16, amp0_1Expr 2 11 k = amp0_12_11 k := by decide +kernel
lemma amp0_12_12_eq : ∀ k : Fin 16, amp0_1Expr 2 12 k = amp0_12_12 k := by decide +kernel
lemma amp0_12_13_eq : ∀ k : Fin 16, amp0_1Expr 2 13 k = amp0_12_13 k := by decide +kernel
lemma amp0_12_14_eq : ∀ k : Fin 16, amp0_1Expr 2 14 k = amp0_12_14 k := by decide +kernel
lemma amp0_12_15_eq : ∀ k : Fin 16, amp0_1Expr 2 15 k = amp0_12_15 k := by decide +kernel
lemma amp0_12_eq (i k : Fin 16) : amp0_1Expr 2 i k = amp0_12 i k := by
  fin_cases i
  · exact amp0_12_0_eq k
  · exact amp0_12_1_eq k
  · exact amp0_12_2_eq k
  · exact amp0_12_3_eq k
  · exact amp0_12_4_eq k
  · exact amp0_12_5_eq k
  · exact amp0_12_6_eq k
  · exact amp0_12_7_eq k
  · exact amp0_12_8_eq k
  · exact amp0_12_9_eq k
  · exact amp0_12_10_eq k
  · exact amp0_12_11_eq k
  · exact amp0_12_12_eq k
  · exact amp0_12_13_eq k
  · exact amp0_12_14_eq k
  · exact amp0_12_15_eq k
lemma amp0_13_0_eq : ∀ k : Fin 16, amp0_1Expr 3 0 k = amp0_13_0 k := by decide +kernel
lemma amp0_13_1_eq : ∀ k : Fin 16, amp0_1Expr 3 1 k = amp0_13_1 k := by decide +kernel
lemma amp0_13_2_eq : ∀ k : Fin 16, amp0_1Expr 3 2 k = amp0_13_2 k := by decide +kernel
lemma amp0_13_3_eq : ∀ k : Fin 16, amp0_1Expr 3 3 k = amp0_13_3 k := by decide +kernel
lemma amp0_13_4_eq : ∀ k : Fin 16, amp0_1Expr 3 4 k = amp0_13_4 k := by decide +kernel
lemma amp0_13_5_eq : ∀ k : Fin 16, amp0_1Expr 3 5 k = amp0_13_5 k := by decide +kernel
lemma amp0_13_6_eq : ∀ k : Fin 16, amp0_1Expr 3 6 k = amp0_13_6 k := by decide +kernel
lemma amp0_13_7_eq : ∀ k : Fin 16, amp0_1Expr 3 7 k = amp0_13_7 k := by decide +kernel
lemma amp0_13_8_eq : ∀ k : Fin 16, amp0_1Expr 3 8 k = amp0_13_8 k := by decide +kernel
lemma amp0_13_9_eq : ∀ k : Fin 16, amp0_1Expr 3 9 k = amp0_13_9 k := by decide +kernel
lemma amp0_13_10_eq : ∀ k : Fin 16, amp0_1Expr 3 10 k = amp0_13_10 k := by decide +kernel
lemma amp0_13_11_eq : ∀ k : Fin 16, amp0_1Expr 3 11 k = amp0_13_11 k := by decide +kernel
lemma amp0_13_12_eq : ∀ k : Fin 16, amp0_1Expr 3 12 k = amp0_13_12 k := by decide +kernel
lemma amp0_13_13_eq : ∀ k : Fin 16, amp0_1Expr 3 13 k = amp0_13_13 k := by decide +kernel
lemma amp0_13_14_eq : ∀ k : Fin 16, amp0_1Expr 3 14 k = amp0_13_14 k := by decide +kernel
lemma amp0_13_15_eq : ∀ k : Fin 16, amp0_1Expr 3 15 k = amp0_13_15 k := by decide +kernel
lemma amp0_13_eq (i k : Fin 16) : amp0_1Expr 3 i k = amp0_13 i k := by
  fin_cases i
  · exact amp0_13_0_eq k
  · exact amp0_13_1_eq k
  · exact amp0_13_2_eq k
  · exact amp0_13_3_eq k
  · exact amp0_13_4_eq k
  · exact amp0_13_5_eq k
  · exact amp0_13_6_eq k
  · exact amp0_13_7_eq k
  · exact amp0_13_8_eq k
  · exact amp0_13_9_eq k
  · exact amp0_13_10_eq k
  · exact amp0_13_11_eq k
  · exact amp0_13_12_eq k
  · exact amp0_13_13_eq k
  · exact amp0_13_14_eq k
  · exact amp0_13_15_eq k
lemma amp0_14_0_eq : ∀ k : Fin 16, amp0_1Expr 4 0 k = amp0_14_0 k := by decide +kernel
lemma amp0_14_1_eq : ∀ k : Fin 16, amp0_1Expr 4 1 k = amp0_14_1 k := by decide +kernel
lemma amp0_14_2_eq : ∀ k : Fin 16, amp0_1Expr 4 2 k = amp0_14_2 k := by decide +kernel
lemma amp0_14_3_eq : ∀ k : Fin 16, amp0_1Expr 4 3 k = amp0_14_3 k := by decide +kernel
lemma amp0_14_4_eq : ∀ k : Fin 16, amp0_1Expr 4 4 k = amp0_14_4 k := by decide +kernel
lemma amp0_14_5_eq : ∀ k : Fin 16, amp0_1Expr 4 5 k = amp0_14_5 k := by decide +kernel
lemma amp0_14_6_eq : ∀ k : Fin 16, amp0_1Expr 4 6 k = amp0_14_6 k := by decide +kernel
lemma amp0_14_7_eq : ∀ k : Fin 16, amp0_1Expr 4 7 k = amp0_14_7 k := by decide +kernel
lemma amp0_14_8_eq : ∀ k : Fin 16, amp0_1Expr 4 8 k = amp0_14_8 k := by decide +kernel
lemma amp0_14_9_eq : ∀ k : Fin 16, amp0_1Expr 4 9 k = amp0_14_9 k := by decide +kernel
lemma amp0_14_10_eq : ∀ k : Fin 16, amp0_1Expr 4 10 k = amp0_14_10 k := by decide +kernel
lemma amp0_14_11_eq : ∀ k : Fin 16, amp0_1Expr 4 11 k = amp0_14_11 k := by decide +kernel
lemma amp0_14_12_eq : ∀ k : Fin 16, amp0_1Expr 4 12 k = amp0_14_12 k := by decide +kernel
lemma amp0_14_13_eq : ∀ k : Fin 16, amp0_1Expr 4 13 k = amp0_14_13 k := by decide +kernel
lemma amp0_14_14_eq : ∀ k : Fin 16, amp0_1Expr 4 14 k = amp0_14_14 k := by decide +kernel
lemma amp0_14_15_eq : ∀ k : Fin 16, amp0_1Expr 4 15 k = amp0_14_15 k := by decide +kernel
lemma amp0_14_eq (i k : Fin 16) : amp0_1Expr 4 i k = amp0_14 i k := by
  fin_cases i
  · exact amp0_14_0_eq k
  · exact amp0_14_1_eq k
  · exact amp0_14_2_eq k
  · exact amp0_14_3_eq k
  · exact amp0_14_4_eq k
  · exact amp0_14_5_eq k
  · exact amp0_14_6_eq k
  · exact amp0_14_7_eq k
  · exact amp0_14_8_eq k
  · exact amp0_14_9_eq k
  · exact amp0_14_10_eq k
  · exact amp0_14_11_eq k
  · exact amp0_14_12_eq k
  · exact amp0_14_13_eq k
  · exact amp0_14_14_eq k
  · exact amp0_14_15_eq k
lemma amp0_15_0_eq : ∀ k : Fin 16, amp0_1Expr 5 0 k = amp0_15_0 k := by decide +kernel
lemma amp0_15_1_eq : ∀ k : Fin 16, amp0_1Expr 5 1 k = amp0_15_1 k := by decide +kernel
lemma amp0_15_2_eq : ∀ k : Fin 16, amp0_1Expr 5 2 k = amp0_15_2 k := by decide +kernel
lemma amp0_15_3_eq : ∀ k : Fin 16, amp0_1Expr 5 3 k = amp0_15_3 k := by decide +kernel
lemma amp0_15_4_eq : ∀ k : Fin 16, amp0_1Expr 5 4 k = amp0_15_4 k := by decide +kernel
lemma amp0_15_5_eq : ∀ k : Fin 16, amp0_1Expr 5 5 k = amp0_15_5 k := by decide +kernel
lemma amp0_15_6_eq : ∀ k : Fin 16, amp0_1Expr 5 6 k = amp0_15_6 k := by decide +kernel
lemma amp0_15_7_eq : ∀ k : Fin 16, amp0_1Expr 5 7 k = amp0_15_7 k := by decide +kernel
lemma amp0_15_8_eq : ∀ k : Fin 16, amp0_1Expr 5 8 k = amp0_15_8 k := by decide +kernel
lemma amp0_15_9_eq : ∀ k : Fin 16, amp0_1Expr 5 9 k = amp0_15_9 k := by decide +kernel
lemma amp0_15_10_eq : ∀ k : Fin 16, amp0_1Expr 5 10 k = amp0_15_10 k := by decide +kernel
lemma amp0_15_11_eq : ∀ k : Fin 16, amp0_1Expr 5 11 k = amp0_15_11 k := by decide +kernel
lemma amp0_15_12_eq : ∀ k : Fin 16, amp0_1Expr 5 12 k = amp0_15_12 k := by decide +kernel
lemma amp0_15_13_eq : ∀ k : Fin 16, amp0_1Expr 5 13 k = amp0_15_13 k := by decide +kernel
lemma amp0_15_14_eq : ∀ k : Fin 16, amp0_1Expr 5 14 k = amp0_15_14 k := by decide +kernel
lemma amp0_15_15_eq : ∀ k : Fin 16, amp0_1Expr 5 15 k = amp0_15_15 k := by decide +kernel
lemma amp0_15_eq (i k : Fin 16) : amp0_1Expr 5 i k = amp0_15 i k := by
  fin_cases i
  · exact amp0_15_0_eq k
  · exact amp0_15_1_eq k
  · exact amp0_15_2_eq k
  · exact amp0_15_3_eq k
  · exact amp0_15_4_eq k
  · exact amp0_15_5_eq k
  · exact amp0_15_6_eq k
  · exact amp0_15_7_eq k
  · exact amp0_15_8_eq k
  · exact amp0_15_9_eq k
  · exact amp0_15_10_eq k
  · exact amp0_15_11_eq k
  · exact amp0_15_12_eq k
  · exact amp0_15_13_eq k
  · exact amp0_15_14_eq k
  · exact amp0_15_15_eq k
lemma amp0_1_eq_g_oai (j : Fin 6) (i k : Fin 16) : amp0_1Expr j i k = amp0_1 j i k := by
  fin_cases j
  · exact amp0_10_eq_g i k
  · exact amp0_11_eq i k
  · exact amp0_12_eq i k
  · exact amp0_13_eq i k
  · exact amp0_14_eq i k
  · exact amp0_15_eq i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.amp0_1_eq_g_oai := @OAI.SharpPlanar.CachedData.amp0_1_eq_g_oai
