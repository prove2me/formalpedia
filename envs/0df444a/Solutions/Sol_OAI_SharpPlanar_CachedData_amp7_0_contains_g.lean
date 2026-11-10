-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.amp7_0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:00:50.299131+00:00
-- url     : https://prove2.me/submissions/71895892-37aa-43cd-a4ab-d5e598c38dba

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G103
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aLookup_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bLookup_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_waveAmplitudeBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g

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
lemma amp7_00_0_eq : ∀ k : Fin 16, amp7_0Expr 0 0 k = amp7_00_0 k := by decide +kernel
lemma amp7_00_1_eq : ∀ k : Fin 16, amp7_0Expr 0 1 k = amp7_00_1 k := by decide +kernel
lemma amp7_00_2_eq : ∀ k : Fin 16, amp7_0Expr 0 2 k = amp7_00_2 k := by decide +kernel
lemma amp7_00_3_eq : ∀ k : Fin 16, amp7_0Expr 0 3 k = amp7_00_3 k := by decide +kernel
lemma amp7_00_4_eq : ∀ k : Fin 16, amp7_0Expr 0 4 k = amp7_00_4 k := by decide +kernel
lemma amp7_00_5_eq : ∀ k : Fin 16, amp7_0Expr 0 5 k = amp7_00_5 k := by decide +kernel
lemma amp7_00_6_eq : ∀ k : Fin 16, amp7_0Expr 0 6 k = amp7_00_6 k := by decide +kernel
lemma amp7_00_7_eq : ∀ k : Fin 16, amp7_0Expr 0 7 k = amp7_00_7 k := by decide +kernel
lemma amp7_00_8_eq : ∀ k : Fin 16, amp7_0Expr 0 8 k = amp7_00_8 k := by decide +kernel
lemma amp7_00_9_eq : ∀ k : Fin 16, amp7_0Expr 0 9 k = amp7_00_9 k := by decide +kernel
lemma amp7_00_10_eq : ∀ k : Fin 16, amp7_0Expr 0 10 k = amp7_00_10 k := by decide +kernel
lemma amp7_00_11_eq : ∀ k : Fin 16, amp7_0Expr 0 11 k = amp7_00_11 k := by decide +kernel
lemma amp7_00_12_eq : ∀ k : Fin 16, amp7_0Expr 0 12 k = amp7_00_12 k := by decide +kernel
lemma amp7_00_13_eq : ∀ k : Fin 16, amp7_0Expr 0 13 k = amp7_00_13 k := by decide +kernel
lemma amp7_00_14_eq : ∀ k : Fin 16, amp7_0Expr 0 14 k = amp7_00_14 k := by decide +kernel
lemma amp7_00_15_eq : ∀ k : Fin 16, amp7_0Expr 0 15 k = amp7_00_15 k := by decide +kernel
lemma amp7_00_eq (i k : Fin 16) : amp7_0Expr 0 i k = amp7_00 i k := by
  fin_cases i
  · exact amp7_00_0_eq k
  · exact amp7_00_1_eq k
  · exact amp7_00_2_eq k
  · exact amp7_00_3_eq k
  · exact amp7_00_4_eq k
  · exact amp7_00_5_eq k
  · exact amp7_00_6_eq k
  · exact amp7_00_7_eq k
  · exact amp7_00_8_eq k
  · exact amp7_00_9_eq k
  · exact amp7_00_10_eq k
  · exact amp7_00_11_eq k
  · exact amp7_00_12_eq k
  · exact amp7_00_13_eq k
  · exact amp7_00_14_eq k
  · exact amp7_00_15_eq k
lemma amp7_01_0_eq : ∀ k : Fin 16, amp7_0Expr 1 0 k = amp7_01_0 k := by decide +kernel
lemma amp7_01_1_eq : ∀ k : Fin 16, amp7_0Expr 1 1 k = amp7_01_1 k := by decide +kernel
lemma amp7_01_2_eq : ∀ k : Fin 16, amp7_0Expr 1 2 k = amp7_01_2 k := by decide +kernel
lemma amp7_01_3_eq : ∀ k : Fin 16, amp7_0Expr 1 3 k = amp7_01_3 k := by decide +kernel
lemma amp7_01_4_eq : ∀ k : Fin 16, amp7_0Expr 1 4 k = amp7_01_4 k := by decide +kernel
lemma amp7_01_5_eq : ∀ k : Fin 16, amp7_0Expr 1 5 k = amp7_01_5 k := by decide +kernel
lemma amp7_01_6_eq : ∀ k : Fin 16, amp7_0Expr 1 6 k = amp7_01_6 k := by decide +kernel
lemma amp7_01_7_eq : ∀ k : Fin 16, amp7_0Expr 1 7 k = amp7_01_7 k := by decide +kernel
lemma amp7_01_8_eq : ∀ k : Fin 16, amp7_0Expr 1 8 k = amp7_01_8 k := by decide +kernel
lemma amp7_01_9_eq : ∀ k : Fin 16, amp7_0Expr 1 9 k = amp7_01_9 k := by decide +kernel
lemma amp7_01_10_eq : ∀ k : Fin 16, amp7_0Expr 1 10 k = amp7_01_10 k := by decide +kernel
lemma amp7_01_11_eq : ∀ k : Fin 16, amp7_0Expr 1 11 k = amp7_01_11 k := by decide +kernel
lemma amp7_01_12_eq : ∀ k : Fin 16, amp7_0Expr 1 12 k = amp7_01_12 k := by decide +kernel
lemma amp7_01_13_eq : ∀ k : Fin 16, amp7_0Expr 1 13 k = amp7_01_13 k := by decide +kernel
lemma amp7_01_14_eq : ∀ k : Fin 16, amp7_0Expr 1 14 k = amp7_01_14 k := by decide +kernel
lemma amp7_01_15_eq : ∀ k : Fin 16, amp7_0Expr 1 15 k = amp7_01_15 k := by decide +kernel
lemma amp7_01_eq (i k : Fin 16) : amp7_0Expr 1 i k = amp7_01 i k := by
  fin_cases i
  · exact amp7_01_0_eq k
  · exact amp7_01_1_eq k
  · exact amp7_01_2_eq k
  · exact amp7_01_3_eq k
  · exact amp7_01_4_eq k
  · exact amp7_01_5_eq k
  · exact amp7_01_6_eq k
  · exact amp7_01_7_eq k
  · exact amp7_01_8_eq k
  · exact amp7_01_9_eq k
  · exact amp7_01_10_eq k
  · exact amp7_01_11_eq k
  · exact amp7_01_12_eq k
  · exact amp7_01_13_eq k
  · exact amp7_01_14_eq k
  · exact amp7_01_15_eq k
lemma amp7_02_0_eq : ∀ k : Fin 16, amp7_0Expr 2 0 k = amp7_02_0 k := by decide +kernel
lemma amp7_02_1_eq : ∀ k : Fin 16, amp7_0Expr 2 1 k = amp7_02_1 k := by decide +kernel
lemma amp7_02_2_eq : ∀ k : Fin 16, amp7_0Expr 2 2 k = amp7_02_2 k := by decide +kernel
lemma amp7_02_3_eq : ∀ k : Fin 16, amp7_0Expr 2 3 k = amp7_02_3 k := by decide +kernel
lemma amp7_02_4_eq : ∀ k : Fin 16, amp7_0Expr 2 4 k = amp7_02_4 k := by decide +kernel
lemma amp7_02_5_eq : ∀ k : Fin 16, amp7_0Expr 2 5 k = amp7_02_5 k := by decide +kernel
lemma amp7_02_6_eq : ∀ k : Fin 16, amp7_0Expr 2 6 k = amp7_02_6 k := by decide +kernel
lemma amp7_02_7_eq : ∀ k : Fin 16, amp7_0Expr 2 7 k = amp7_02_7 k := by decide +kernel
lemma amp7_02_8_eq : ∀ k : Fin 16, amp7_0Expr 2 8 k = amp7_02_8 k := by decide +kernel
lemma amp7_02_9_eq : ∀ k : Fin 16, amp7_0Expr 2 9 k = amp7_02_9 k := by decide +kernel
lemma amp7_02_10_eq : ∀ k : Fin 16, amp7_0Expr 2 10 k = amp7_02_10 k := by decide +kernel
lemma amp7_02_11_eq : ∀ k : Fin 16, amp7_0Expr 2 11 k = amp7_02_11 k := by decide +kernel
lemma amp7_02_12_eq : ∀ k : Fin 16, amp7_0Expr 2 12 k = amp7_02_12 k := by decide +kernel
lemma amp7_02_13_eq : ∀ k : Fin 16, amp7_0Expr 2 13 k = amp7_02_13 k := by decide +kernel
lemma amp7_02_14_eq : ∀ k : Fin 16, amp7_0Expr 2 14 k = amp7_02_14 k := by decide +kernel
lemma amp7_02_15_eq : ∀ k : Fin 16, amp7_0Expr 2 15 k = amp7_02_15 k := by decide +kernel
lemma amp7_02_eq (i k : Fin 16) : amp7_0Expr 2 i k = amp7_02 i k := by
  fin_cases i
  · exact amp7_02_0_eq k
  · exact amp7_02_1_eq k
  · exact amp7_02_2_eq k
  · exact amp7_02_3_eq k
  · exact amp7_02_4_eq k
  · exact amp7_02_5_eq k
  · exact amp7_02_6_eq k
  · exact amp7_02_7_eq k
  · exact amp7_02_8_eq k
  · exact amp7_02_9_eq k
  · exact amp7_02_10_eq k
  · exact amp7_02_11_eq k
  · exact amp7_02_12_eq k
  · exact amp7_02_13_eq k
  · exact amp7_02_14_eq k
  · exact amp7_02_15_eq k
lemma amp7_03_0_eq : ∀ k : Fin 16, amp7_0Expr 3 0 k = amp7_03_0 k := by decide +kernel
lemma amp7_03_1_eq : ∀ k : Fin 16, amp7_0Expr 3 1 k = amp7_03_1 k := by decide +kernel
lemma amp7_03_2_eq : ∀ k : Fin 16, amp7_0Expr 3 2 k = amp7_03_2 k := by decide +kernel
lemma amp7_03_3_eq : ∀ k : Fin 16, amp7_0Expr 3 3 k = amp7_03_3 k := by decide +kernel
lemma amp7_03_4_eq : ∀ k : Fin 16, amp7_0Expr 3 4 k = amp7_03_4 k := by decide +kernel
lemma amp7_03_5_eq : ∀ k : Fin 16, amp7_0Expr 3 5 k = amp7_03_5 k := by decide +kernel
lemma amp7_03_6_eq : ∀ k : Fin 16, amp7_0Expr 3 6 k = amp7_03_6 k := by decide +kernel
lemma amp7_03_7_eq : ∀ k : Fin 16, amp7_0Expr 3 7 k = amp7_03_7 k := by decide +kernel
lemma amp7_03_8_eq : ∀ k : Fin 16, amp7_0Expr 3 8 k = amp7_03_8 k := by decide +kernel
lemma amp7_03_9_eq : ∀ k : Fin 16, amp7_0Expr 3 9 k = amp7_03_9 k := by decide +kernel
lemma amp7_03_10_eq : ∀ k : Fin 16, amp7_0Expr 3 10 k = amp7_03_10 k := by decide +kernel
lemma amp7_03_11_eq : ∀ k : Fin 16, amp7_0Expr 3 11 k = amp7_03_11 k := by decide +kernel
lemma amp7_03_12_eq : ∀ k : Fin 16, amp7_0Expr 3 12 k = amp7_03_12 k := by decide +kernel
lemma amp7_03_13_eq : ∀ k : Fin 16, amp7_0Expr 3 13 k = amp7_03_13 k := by decide +kernel
lemma amp7_03_14_eq : ∀ k : Fin 16, amp7_0Expr 3 14 k = amp7_03_14 k := by decide +kernel
lemma amp7_03_15_eq : ∀ k : Fin 16, amp7_0Expr 3 15 k = amp7_03_15 k := by decide +kernel
lemma amp7_03_eq (i k : Fin 16) : amp7_0Expr 3 i k = amp7_03 i k := by
  fin_cases i
  · exact amp7_03_0_eq k
  · exact amp7_03_1_eq k
  · exact amp7_03_2_eq k
  · exact amp7_03_3_eq k
  · exact amp7_03_4_eq k
  · exact amp7_03_5_eq k
  · exact amp7_03_6_eq k
  · exact amp7_03_7_eq k
  · exact amp7_03_8_eq k
  · exact amp7_03_9_eq k
  · exact amp7_03_10_eq k
  · exact amp7_03_11_eq k
  · exact amp7_03_12_eq k
  · exact amp7_03_13_eq k
  · exact amp7_03_14_eq k
  · exact amp7_03_15_eq k
lemma amp7_04_0_eq : ∀ k : Fin 16, amp7_0Expr 4 0 k = amp7_04_0 k := by decide +kernel
lemma amp7_04_1_eq : ∀ k : Fin 16, amp7_0Expr 4 1 k = amp7_04_1 k := by decide +kernel
lemma amp7_04_2_eq : ∀ k : Fin 16, amp7_0Expr 4 2 k = amp7_04_2 k := by decide +kernel
lemma amp7_04_3_eq : ∀ k : Fin 16, amp7_0Expr 4 3 k = amp7_04_3 k := by decide +kernel
lemma amp7_04_4_eq : ∀ k : Fin 16, amp7_0Expr 4 4 k = amp7_04_4 k := by decide +kernel
lemma amp7_04_5_eq : ∀ k : Fin 16, amp7_0Expr 4 5 k = amp7_04_5 k := by decide +kernel
lemma amp7_04_6_eq : ∀ k : Fin 16, amp7_0Expr 4 6 k = amp7_04_6 k := by decide +kernel
lemma amp7_04_7_eq : ∀ k : Fin 16, amp7_0Expr 4 7 k = amp7_04_7 k := by decide +kernel
lemma amp7_04_8_eq : ∀ k : Fin 16, amp7_0Expr 4 8 k = amp7_04_8 k := by decide +kernel
lemma amp7_04_9_eq : ∀ k : Fin 16, amp7_0Expr 4 9 k = amp7_04_9 k := by decide +kernel
lemma amp7_04_10_eq : ∀ k : Fin 16, amp7_0Expr 4 10 k = amp7_04_10 k := by decide +kernel
lemma amp7_04_11_eq : ∀ k : Fin 16, amp7_0Expr 4 11 k = amp7_04_11 k := by decide +kernel
lemma amp7_04_12_eq : ∀ k : Fin 16, amp7_0Expr 4 12 k = amp7_04_12 k := by decide +kernel
lemma amp7_04_13_eq : ∀ k : Fin 16, amp7_0Expr 4 13 k = amp7_04_13 k := by decide +kernel
lemma amp7_04_14_eq : ∀ k : Fin 16, amp7_0Expr 4 14 k = amp7_04_14 k := by decide +kernel
lemma amp7_04_15_eq : ∀ k : Fin 16, amp7_0Expr 4 15 k = amp7_04_15 k := by decide +kernel
lemma amp7_04_eq (i k : Fin 16) : amp7_0Expr 4 i k = amp7_04 i k := by
  fin_cases i
  · exact amp7_04_0_eq k
  · exact amp7_04_1_eq k
  · exact amp7_04_2_eq k
  · exact amp7_04_3_eq k
  · exact amp7_04_4_eq k
  · exact amp7_04_5_eq k
  · exact amp7_04_6_eq k
  · exact amp7_04_7_eq k
  · exact amp7_04_8_eq k
  · exact amp7_04_9_eq k
  · exact amp7_04_10_eq k
  · exact amp7_04_11_eq k
  · exact amp7_04_12_eq k
  · exact amp7_04_13_eq k
  · exact amp7_04_14_eq k
  · exact amp7_04_15_eq k
lemma amp7_05_0_eq : ∀ k : Fin 16, amp7_0Expr 5 0 k = amp7_05_0 k := by decide +kernel
lemma amp7_05_1_eq : ∀ k : Fin 16, amp7_0Expr 5 1 k = amp7_05_1 k := by decide +kernel
lemma amp7_05_2_eq : ∀ k : Fin 16, amp7_0Expr 5 2 k = amp7_05_2 k := by decide +kernel
lemma amp7_05_3_eq : ∀ k : Fin 16, amp7_0Expr 5 3 k = amp7_05_3 k := by decide +kernel
lemma amp7_05_4_eq : ∀ k : Fin 16, amp7_0Expr 5 4 k = amp7_05_4 k := by decide +kernel
lemma amp7_05_5_eq : ∀ k : Fin 16, amp7_0Expr 5 5 k = amp7_05_5 k := by decide +kernel
lemma amp7_05_6_eq : ∀ k : Fin 16, amp7_0Expr 5 6 k = amp7_05_6 k := by decide +kernel
lemma amp7_05_7_eq : ∀ k : Fin 16, amp7_0Expr 5 7 k = amp7_05_7 k := by decide +kernel
lemma amp7_05_8_eq : ∀ k : Fin 16, amp7_0Expr 5 8 k = amp7_05_8 k := by decide +kernel
lemma amp7_05_9_eq : ∀ k : Fin 16, amp7_0Expr 5 9 k = amp7_05_9 k := by decide +kernel
lemma amp7_05_10_eq : ∀ k : Fin 16, amp7_0Expr 5 10 k = amp7_05_10 k := by decide +kernel
lemma amp7_05_11_eq : ∀ k : Fin 16, amp7_0Expr 5 11 k = amp7_05_11 k := by decide +kernel
lemma amp7_05_12_eq : ∀ k : Fin 16, amp7_0Expr 5 12 k = amp7_05_12 k := by decide +kernel
lemma amp7_05_13_eq : ∀ k : Fin 16, amp7_0Expr 5 13 k = amp7_05_13 k := by decide +kernel
lemma amp7_05_14_eq : ∀ k : Fin 16, amp7_0Expr 5 14 k = amp7_05_14 k := by decide +kernel
lemma amp7_05_15_eq : ∀ k : Fin 16, amp7_0Expr 5 15 k = amp7_05_15 k := by decide +kernel
lemma amp7_05_eq (i k : Fin 16) : amp7_0Expr 5 i k = amp7_05 i k := by
  fin_cases i
  · exact amp7_05_0_eq k
  · exact amp7_05_1_eq k
  · exact amp7_05_2_eq k
  · exact amp7_05_3_eq k
  · exact amp7_05_4_eq k
  · exact amp7_05_5_eq k
  · exact amp7_05_6_eq k
  · exact amp7_05_7_eq k
  · exact amp7_05_8_eq k
  · exact amp7_05_9_eq k
  · exact amp7_05_10_eq k
  · exact amp7_05_11_eq k
  · exact amp7_05_12_eq k
  · exact amp7_05_13_eq k
  · exact amp7_05_14_eq k
  · exact amp7_05_15_eq k
lemma amp7_0_eq (j : Fin 6) (i k : Fin 16) : amp7_0Expr j i k = amp7_0 j i k := by
  fin_cases j
  · exact amp7_00_eq i k
  · exact amp7_01_eq i k
  · exact amp7_02_eq i k
  · exact amp7_03_eq i k
  · exact amp7_04_eq i k
  · exact amp7_05_eq i k
lemma amp7_0_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (amp7_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude false 7 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← amp7_0_eq]
  exact CBox.contains_mul_g (rcast_contains_g (weightRows_contains_g i k))
    (waveAmplitudeBox_contains_g (gridRows_contains_g j i k) (aLookup_contains_g 7 j) (bLookup_contains_g 7 j) false)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.amp7_0_contains_g_oai := @OAI.SharpPlanar.CachedData.amp7_0_contains_g_oai
