-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.amp0_0_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T06:08:09.128491+00:00
-- url     : https://prove2.me/submissions/586de4b9-88f9-4639-9e95-f5e1b0de70e5

import Mathlib
import Definitions.Def_OAIQ098G103
import Theorems.Thm_OAI_SharpPlanar_CachedData_amp0_03_eq_g

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
lemma amp0_00_0_eq : ∀ k : Fin 16, amp0_0Expr 0 0 k = amp0_00_0 k := by decide +kernel
lemma amp0_00_1_eq : ∀ k : Fin 16, amp0_0Expr 0 1 k = amp0_00_1 k := by decide +kernel
lemma amp0_00_2_eq : ∀ k : Fin 16, amp0_0Expr 0 2 k = amp0_00_2 k := by decide +kernel
lemma amp0_00_3_eq : ∀ k : Fin 16, amp0_0Expr 0 3 k = amp0_00_3 k := by decide +kernel
lemma amp0_00_4_eq : ∀ k : Fin 16, amp0_0Expr 0 4 k = amp0_00_4 k := by decide +kernel
lemma amp0_00_5_eq : ∀ k : Fin 16, amp0_0Expr 0 5 k = amp0_00_5 k := by decide +kernel
lemma amp0_00_6_eq : ∀ k : Fin 16, amp0_0Expr 0 6 k = amp0_00_6 k := by decide +kernel
lemma amp0_00_7_eq : ∀ k : Fin 16, amp0_0Expr 0 7 k = amp0_00_7 k := by decide +kernel
lemma amp0_00_8_eq : ∀ k : Fin 16, amp0_0Expr 0 8 k = amp0_00_8 k := by decide +kernel
lemma amp0_00_9_eq : ∀ k : Fin 16, amp0_0Expr 0 9 k = amp0_00_9 k := by decide +kernel
lemma amp0_00_10_eq : ∀ k : Fin 16, amp0_0Expr 0 10 k = amp0_00_10 k := by decide +kernel
lemma amp0_00_11_eq : ∀ k : Fin 16, amp0_0Expr 0 11 k = amp0_00_11 k := by decide +kernel
lemma amp0_00_12_eq : ∀ k : Fin 16, amp0_0Expr 0 12 k = amp0_00_12 k := by decide +kernel
lemma amp0_00_13_eq : ∀ k : Fin 16, amp0_0Expr 0 13 k = amp0_00_13 k := by decide +kernel
lemma amp0_00_14_eq : ∀ k : Fin 16, amp0_0Expr 0 14 k = amp0_00_14 k := by decide +kernel
lemma amp0_00_15_eq : ∀ k : Fin 16, amp0_0Expr 0 15 k = amp0_00_15 k := by decide +kernel
lemma amp0_00_eq (i k : Fin 16) : amp0_0Expr 0 i k = amp0_00 i k := by
  fin_cases i
  · exact amp0_00_0_eq k
  · exact amp0_00_1_eq k
  · exact amp0_00_2_eq k
  · exact amp0_00_3_eq k
  · exact amp0_00_4_eq k
  · exact amp0_00_5_eq k
  · exact amp0_00_6_eq k
  · exact amp0_00_7_eq k
  · exact amp0_00_8_eq k
  · exact amp0_00_9_eq k
  · exact amp0_00_10_eq k
  · exact amp0_00_11_eq k
  · exact amp0_00_12_eq k
  · exact amp0_00_13_eq k
  · exact amp0_00_14_eq k
  · exact amp0_00_15_eq k
lemma amp0_01_0_eq : ∀ k : Fin 16, amp0_0Expr 1 0 k = amp0_01_0 k := by decide +kernel
lemma amp0_01_1_eq : ∀ k : Fin 16, amp0_0Expr 1 1 k = amp0_01_1 k := by decide +kernel
lemma amp0_01_2_eq : ∀ k : Fin 16, amp0_0Expr 1 2 k = amp0_01_2 k := by decide +kernel
lemma amp0_01_3_eq : ∀ k : Fin 16, amp0_0Expr 1 3 k = amp0_01_3 k := by decide +kernel
lemma amp0_01_4_eq : ∀ k : Fin 16, amp0_0Expr 1 4 k = amp0_01_4 k := by decide +kernel
lemma amp0_01_5_eq : ∀ k : Fin 16, amp0_0Expr 1 5 k = amp0_01_5 k := by decide +kernel
lemma amp0_01_6_eq : ∀ k : Fin 16, amp0_0Expr 1 6 k = amp0_01_6 k := by decide +kernel
lemma amp0_01_7_eq : ∀ k : Fin 16, amp0_0Expr 1 7 k = amp0_01_7 k := by decide +kernel
lemma amp0_01_8_eq : ∀ k : Fin 16, amp0_0Expr 1 8 k = amp0_01_8 k := by decide +kernel
lemma amp0_01_9_eq : ∀ k : Fin 16, amp0_0Expr 1 9 k = amp0_01_9 k := by decide +kernel
lemma amp0_01_10_eq : ∀ k : Fin 16, amp0_0Expr 1 10 k = amp0_01_10 k := by decide +kernel
lemma amp0_01_11_eq : ∀ k : Fin 16, amp0_0Expr 1 11 k = amp0_01_11 k := by decide +kernel
lemma amp0_01_12_eq : ∀ k : Fin 16, amp0_0Expr 1 12 k = amp0_01_12 k := by decide +kernel
lemma amp0_01_13_eq : ∀ k : Fin 16, amp0_0Expr 1 13 k = amp0_01_13 k := by decide +kernel
lemma amp0_01_14_eq : ∀ k : Fin 16, amp0_0Expr 1 14 k = amp0_01_14 k := by decide +kernel
lemma amp0_01_15_eq : ∀ k : Fin 16, amp0_0Expr 1 15 k = amp0_01_15 k := by decide +kernel
lemma amp0_01_eq (i k : Fin 16) : amp0_0Expr 1 i k = amp0_01 i k := by
  fin_cases i
  · exact amp0_01_0_eq k
  · exact amp0_01_1_eq k
  · exact amp0_01_2_eq k
  · exact amp0_01_3_eq k
  · exact amp0_01_4_eq k
  · exact amp0_01_5_eq k
  · exact amp0_01_6_eq k
  · exact amp0_01_7_eq k
  · exact amp0_01_8_eq k
  · exact amp0_01_9_eq k
  · exact amp0_01_10_eq k
  · exact amp0_01_11_eq k
  · exact amp0_01_12_eq k
  · exact amp0_01_13_eq k
  · exact amp0_01_14_eq k
  · exact amp0_01_15_eq k
lemma amp0_02_0_eq : ∀ k : Fin 16, amp0_0Expr 2 0 k = amp0_02_0 k := by decide +kernel
lemma amp0_02_1_eq : ∀ k : Fin 16, amp0_0Expr 2 1 k = amp0_02_1 k := by decide +kernel
lemma amp0_02_2_eq : ∀ k : Fin 16, amp0_0Expr 2 2 k = amp0_02_2 k := by decide +kernel
lemma amp0_02_3_eq : ∀ k : Fin 16, amp0_0Expr 2 3 k = amp0_02_3 k := by decide +kernel
lemma amp0_02_4_eq : ∀ k : Fin 16, amp0_0Expr 2 4 k = amp0_02_4 k := by decide +kernel
lemma amp0_02_5_eq : ∀ k : Fin 16, amp0_0Expr 2 5 k = amp0_02_5 k := by decide +kernel
lemma amp0_02_6_eq : ∀ k : Fin 16, amp0_0Expr 2 6 k = amp0_02_6 k := by decide +kernel
lemma amp0_02_7_eq : ∀ k : Fin 16, amp0_0Expr 2 7 k = amp0_02_7 k := by decide +kernel
lemma amp0_02_8_eq : ∀ k : Fin 16, amp0_0Expr 2 8 k = amp0_02_8 k := by decide +kernel
lemma amp0_02_9_eq : ∀ k : Fin 16, amp0_0Expr 2 9 k = amp0_02_9 k := by decide +kernel
lemma amp0_02_10_eq : ∀ k : Fin 16, amp0_0Expr 2 10 k = amp0_02_10 k := by decide +kernel
lemma amp0_02_11_eq : ∀ k : Fin 16, amp0_0Expr 2 11 k = amp0_02_11 k := by decide +kernel
lemma amp0_02_12_eq : ∀ k : Fin 16, amp0_0Expr 2 12 k = amp0_02_12 k := by decide +kernel
lemma amp0_02_13_eq : ∀ k : Fin 16, amp0_0Expr 2 13 k = amp0_02_13 k := by decide +kernel
lemma amp0_02_14_eq : ∀ k : Fin 16, amp0_0Expr 2 14 k = amp0_02_14 k := by decide +kernel
lemma amp0_02_15_eq : ∀ k : Fin 16, amp0_0Expr 2 15 k = amp0_02_15 k := by decide +kernel
lemma amp0_02_eq (i k : Fin 16) : amp0_0Expr 2 i k = amp0_02 i k := by
  fin_cases i
  · exact amp0_02_0_eq k
  · exact amp0_02_1_eq k
  · exact amp0_02_2_eq k
  · exact amp0_02_3_eq k
  · exact amp0_02_4_eq k
  · exact amp0_02_5_eq k
  · exact amp0_02_6_eq k
  · exact amp0_02_7_eq k
  · exact amp0_02_8_eq k
  · exact amp0_02_9_eq k
  · exact amp0_02_10_eq k
  · exact amp0_02_11_eq k
  · exact amp0_02_12_eq k
  · exact amp0_02_13_eq k
  · exact amp0_02_14_eq k
  · exact amp0_02_15_eq k
lemma amp0_04_0_eq : ∀ k : Fin 16, amp0_0Expr 4 0 k = amp0_04_0 k := by decide +kernel
lemma amp0_04_1_eq : ∀ k : Fin 16, amp0_0Expr 4 1 k = amp0_04_1 k := by decide +kernel
lemma amp0_04_2_eq : ∀ k : Fin 16, amp0_0Expr 4 2 k = amp0_04_2 k := by decide +kernel
lemma amp0_04_3_eq : ∀ k : Fin 16, amp0_0Expr 4 3 k = amp0_04_3 k := by decide +kernel
lemma amp0_04_4_eq : ∀ k : Fin 16, amp0_0Expr 4 4 k = amp0_04_4 k := by decide +kernel
lemma amp0_04_5_eq : ∀ k : Fin 16, amp0_0Expr 4 5 k = amp0_04_5 k := by decide +kernel
lemma amp0_04_6_eq : ∀ k : Fin 16, amp0_0Expr 4 6 k = amp0_04_6 k := by decide +kernel
lemma amp0_04_7_eq : ∀ k : Fin 16, amp0_0Expr 4 7 k = amp0_04_7 k := by decide +kernel
lemma amp0_04_8_eq : ∀ k : Fin 16, amp0_0Expr 4 8 k = amp0_04_8 k := by decide +kernel
lemma amp0_04_9_eq : ∀ k : Fin 16, amp0_0Expr 4 9 k = amp0_04_9 k := by decide +kernel
lemma amp0_04_10_eq : ∀ k : Fin 16, amp0_0Expr 4 10 k = amp0_04_10 k := by decide +kernel
lemma amp0_04_11_eq : ∀ k : Fin 16, amp0_0Expr 4 11 k = amp0_04_11 k := by decide +kernel
lemma amp0_04_12_eq : ∀ k : Fin 16, amp0_0Expr 4 12 k = amp0_04_12 k := by decide +kernel
lemma amp0_04_13_eq : ∀ k : Fin 16, amp0_0Expr 4 13 k = amp0_04_13 k := by decide +kernel
lemma amp0_04_14_eq : ∀ k : Fin 16, amp0_0Expr 4 14 k = amp0_04_14 k := by decide +kernel
lemma amp0_04_15_eq : ∀ k : Fin 16, amp0_0Expr 4 15 k = amp0_04_15 k := by decide +kernel
lemma amp0_04_eq (i k : Fin 16) : amp0_0Expr 4 i k = amp0_04 i k := by
  fin_cases i
  · exact amp0_04_0_eq k
  · exact amp0_04_1_eq k
  · exact amp0_04_2_eq k
  · exact amp0_04_3_eq k
  · exact amp0_04_4_eq k
  · exact amp0_04_5_eq k
  · exact amp0_04_6_eq k
  · exact amp0_04_7_eq k
  · exact amp0_04_8_eq k
  · exact amp0_04_9_eq k
  · exact amp0_04_10_eq k
  · exact amp0_04_11_eq k
  · exact amp0_04_12_eq k
  · exact amp0_04_13_eq k
  · exact amp0_04_14_eq k
  · exact amp0_04_15_eq k
lemma amp0_05_0_eq : ∀ k : Fin 16, amp0_0Expr 5 0 k = amp0_05_0 k := by decide +kernel
lemma amp0_05_1_eq : ∀ k : Fin 16, amp0_0Expr 5 1 k = amp0_05_1 k := by decide +kernel
lemma amp0_05_2_eq : ∀ k : Fin 16, amp0_0Expr 5 2 k = amp0_05_2 k := by decide +kernel
lemma amp0_05_3_eq : ∀ k : Fin 16, amp0_0Expr 5 3 k = amp0_05_3 k := by decide +kernel
lemma amp0_05_4_eq : ∀ k : Fin 16, amp0_0Expr 5 4 k = amp0_05_4 k := by decide +kernel
lemma amp0_05_5_eq : ∀ k : Fin 16, amp0_0Expr 5 5 k = amp0_05_5 k := by decide +kernel
lemma amp0_05_6_eq : ∀ k : Fin 16, amp0_0Expr 5 6 k = amp0_05_6 k := by decide +kernel
lemma amp0_05_7_eq : ∀ k : Fin 16, amp0_0Expr 5 7 k = amp0_05_7 k := by decide +kernel
lemma amp0_05_8_eq : ∀ k : Fin 16, amp0_0Expr 5 8 k = amp0_05_8 k := by decide +kernel
lemma amp0_05_9_eq : ∀ k : Fin 16, amp0_0Expr 5 9 k = amp0_05_9 k := by decide +kernel
lemma amp0_05_10_eq : ∀ k : Fin 16, amp0_0Expr 5 10 k = amp0_05_10 k := by decide +kernel
lemma amp0_05_11_eq : ∀ k : Fin 16, amp0_0Expr 5 11 k = amp0_05_11 k := by decide +kernel
lemma amp0_05_12_eq : ∀ k : Fin 16, amp0_0Expr 5 12 k = amp0_05_12 k := by decide +kernel
lemma amp0_05_13_eq : ∀ k : Fin 16, amp0_0Expr 5 13 k = amp0_05_13 k := by decide +kernel
lemma amp0_05_14_eq : ∀ k : Fin 16, amp0_0Expr 5 14 k = amp0_05_14 k := by decide +kernel
lemma amp0_05_15_eq : ∀ k : Fin 16, amp0_0Expr 5 15 k = amp0_05_15 k := by decide +kernel
lemma amp0_05_eq (i k : Fin 16) : amp0_0Expr 5 i k = amp0_05 i k := by
  fin_cases i
  · exact amp0_05_0_eq k
  · exact amp0_05_1_eq k
  · exact amp0_05_2_eq k
  · exact amp0_05_3_eq k
  · exact amp0_05_4_eq k
  · exact amp0_05_5_eq k
  · exact amp0_05_6_eq k
  · exact amp0_05_7_eq k
  · exact amp0_05_8_eq k
  · exact amp0_05_9_eq k
  · exact amp0_05_10_eq k
  · exact amp0_05_11_eq k
  · exact amp0_05_12_eq k
  · exact amp0_05_13_eq k
  · exact amp0_05_14_eq k
  · exact amp0_05_15_eq k
lemma amp0_0_eq_g_oai (j : Fin 6) (i k : Fin 16) : amp0_0Expr j i k = amp0_0 j i k := by
  fin_cases j
  · exact amp0_00_eq i k
  · exact amp0_01_eq i k
  · exact amp0_02_eq i k
  · exact amp0_03_eq_g i k
  · exact amp0_04_eq i k
  · exact amp0_05_eq i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.amp0_0_eq_g_oai := @OAI.SharpPlanar.CachedData.amp0_0_eq_g_oai
