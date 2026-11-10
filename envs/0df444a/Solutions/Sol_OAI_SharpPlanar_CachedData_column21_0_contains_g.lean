-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.column21_0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T07:03:12.05488+00:00
-- url     : https://prove2.me/submissions/b5b36edf-90f4-4e2b-abbc-a1a05b2731ba

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G125
import Definitions.Def_OAIQ098G246
import Theorems.Thm_OAI_SharpPlanar_CachedData_power21_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aLookup_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bLookup_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisAlpha_mod_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisBeta_mod_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisFunction_wave_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_waveAmplitudeBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma waveAmplitude_mod (d : Bool) (n j : ℕ) (t : ℝ) :
    waveAmplitude d (n%12) j t = waveAmplitude d n j t := by
  simp only [waveAmplitude,basisAlpha_mod_g,basisBeta_mod_g]

end SharpPlanar.IntegerBasis

end OAI
end

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
lemma amp9_00_0_eq : ∀ k : Fin 16, amp9_0Expr 0 0 k = amp9_00_0 k := by decide +kernel
lemma amp9_00_1_eq : ∀ k : Fin 16, amp9_0Expr 0 1 k = amp9_00_1 k := by decide +kernel
lemma amp9_00_2_eq : ∀ k : Fin 16, amp9_0Expr 0 2 k = amp9_00_2 k := by decide +kernel
lemma amp9_00_3_eq : ∀ k : Fin 16, amp9_0Expr 0 3 k = amp9_00_3 k := by decide +kernel
lemma amp9_00_4_eq : ∀ k : Fin 16, amp9_0Expr 0 4 k = amp9_00_4 k := by decide +kernel
lemma amp9_00_5_eq : ∀ k : Fin 16, amp9_0Expr 0 5 k = amp9_00_5 k := by decide +kernel
lemma amp9_00_6_eq : ∀ k : Fin 16, amp9_0Expr 0 6 k = amp9_00_6 k := by decide +kernel
lemma amp9_00_7_eq : ∀ k : Fin 16, amp9_0Expr 0 7 k = amp9_00_7 k := by decide +kernel
lemma amp9_00_8_eq : ∀ k : Fin 16, amp9_0Expr 0 8 k = amp9_00_8 k := by decide +kernel
lemma amp9_00_9_eq : ∀ k : Fin 16, amp9_0Expr 0 9 k = amp9_00_9 k := by decide +kernel
lemma amp9_00_10_eq : ∀ k : Fin 16, amp9_0Expr 0 10 k = amp9_00_10 k := by decide +kernel
lemma amp9_00_11_eq : ∀ k : Fin 16, amp9_0Expr 0 11 k = amp9_00_11 k := by decide +kernel
lemma amp9_00_12_eq : ∀ k : Fin 16, amp9_0Expr 0 12 k = amp9_00_12 k := by decide +kernel
lemma amp9_00_13_eq : ∀ k : Fin 16, amp9_0Expr 0 13 k = amp9_00_13 k := by decide +kernel
lemma amp9_00_14_eq : ∀ k : Fin 16, amp9_0Expr 0 14 k = amp9_00_14 k := by decide +kernel
lemma amp9_00_15_eq : ∀ k : Fin 16, amp9_0Expr 0 15 k = amp9_00_15 k := by decide +kernel
lemma amp9_00_eq (i k : Fin 16) : amp9_0Expr 0 i k = amp9_00 i k := by
  fin_cases i
  · exact amp9_00_0_eq k
  · exact amp9_00_1_eq k
  · exact amp9_00_2_eq k
  · exact amp9_00_3_eq k
  · exact amp9_00_4_eq k
  · exact amp9_00_5_eq k
  · exact amp9_00_6_eq k
  · exact amp9_00_7_eq k
  · exact amp9_00_8_eq k
  · exact amp9_00_9_eq k
  · exact amp9_00_10_eq k
  · exact amp9_00_11_eq k
  · exact amp9_00_12_eq k
  · exact amp9_00_13_eq k
  · exact amp9_00_14_eq k
  · exact amp9_00_15_eq k
lemma amp9_01_0_eq : ∀ k : Fin 16, amp9_0Expr 1 0 k = amp9_01_0 k := by decide +kernel
lemma amp9_01_1_eq : ∀ k : Fin 16, amp9_0Expr 1 1 k = amp9_01_1 k := by decide +kernel
lemma amp9_01_2_eq : ∀ k : Fin 16, amp9_0Expr 1 2 k = amp9_01_2 k := by decide +kernel
lemma amp9_01_3_eq : ∀ k : Fin 16, amp9_0Expr 1 3 k = amp9_01_3 k := by decide +kernel
lemma amp9_01_4_eq : ∀ k : Fin 16, amp9_0Expr 1 4 k = amp9_01_4 k := by decide +kernel
lemma amp9_01_5_eq : ∀ k : Fin 16, amp9_0Expr 1 5 k = amp9_01_5 k := by decide +kernel
lemma amp9_01_6_eq : ∀ k : Fin 16, amp9_0Expr 1 6 k = amp9_01_6 k := by decide +kernel
lemma amp9_01_7_eq : ∀ k : Fin 16, amp9_0Expr 1 7 k = amp9_01_7 k := by decide +kernel
lemma amp9_01_8_eq : ∀ k : Fin 16, amp9_0Expr 1 8 k = amp9_01_8 k := by decide +kernel
lemma amp9_01_9_eq : ∀ k : Fin 16, amp9_0Expr 1 9 k = amp9_01_9 k := by decide +kernel
lemma amp9_01_10_eq : ∀ k : Fin 16, amp9_0Expr 1 10 k = amp9_01_10 k := by decide +kernel
lemma amp9_01_11_eq : ∀ k : Fin 16, amp9_0Expr 1 11 k = amp9_01_11 k := by decide +kernel
lemma amp9_01_12_eq : ∀ k : Fin 16, amp9_0Expr 1 12 k = amp9_01_12 k := by decide +kernel
lemma amp9_01_13_eq : ∀ k : Fin 16, amp9_0Expr 1 13 k = amp9_01_13 k := by decide +kernel
lemma amp9_01_14_eq : ∀ k : Fin 16, amp9_0Expr 1 14 k = amp9_01_14 k := by decide +kernel
lemma amp9_01_15_eq : ∀ k : Fin 16, amp9_0Expr 1 15 k = amp9_01_15 k := by decide +kernel
lemma amp9_01_eq (i k : Fin 16) : amp9_0Expr 1 i k = amp9_01 i k := by
  fin_cases i
  · exact amp9_01_0_eq k
  · exact amp9_01_1_eq k
  · exact amp9_01_2_eq k
  · exact amp9_01_3_eq k
  · exact amp9_01_4_eq k
  · exact amp9_01_5_eq k
  · exact amp9_01_6_eq k
  · exact amp9_01_7_eq k
  · exact amp9_01_8_eq k
  · exact amp9_01_9_eq k
  · exact amp9_01_10_eq k
  · exact amp9_01_11_eq k
  · exact amp9_01_12_eq k
  · exact amp9_01_13_eq k
  · exact amp9_01_14_eq k
  · exact amp9_01_15_eq k
lemma amp9_02_0_eq : ∀ k : Fin 16, amp9_0Expr 2 0 k = amp9_02_0 k := by decide +kernel
lemma amp9_02_1_eq : ∀ k : Fin 16, amp9_0Expr 2 1 k = amp9_02_1 k := by decide +kernel
lemma amp9_02_2_eq : ∀ k : Fin 16, amp9_0Expr 2 2 k = amp9_02_2 k := by decide +kernel
lemma amp9_02_3_eq : ∀ k : Fin 16, amp9_0Expr 2 3 k = amp9_02_3 k := by decide +kernel
lemma amp9_02_4_eq : ∀ k : Fin 16, amp9_0Expr 2 4 k = amp9_02_4 k := by decide +kernel
lemma amp9_02_5_eq : ∀ k : Fin 16, amp9_0Expr 2 5 k = amp9_02_5 k := by decide +kernel
lemma amp9_02_6_eq : ∀ k : Fin 16, amp9_0Expr 2 6 k = amp9_02_6 k := by decide +kernel
lemma amp9_02_7_eq : ∀ k : Fin 16, amp9_0Expr 2 7 k = amp9_02_7 k := by decide +kernel
lemma amp9_02_8_eq : ∀ k : Fin 16, amp9_0Expr 2 8 k = amp9_02_8 k := by decide +kernel
lemma amp9_02_9_eq : ∀ k : Fin 16, amp9_0Expr 2 9 k = amp9_02_9 k := by decide +kernel
lemma amp9_02_10_eq : ∀ k : Fin 16, amp9_0Expr 2 10 k = amp9_02_10 k := by decide +kernel
lemma amp9_02_11_eq : ∀ k : Fin 16, amp9_0Expr 2 11 k = amp9_02_11 k := by decide +kernel
lemma amp9_02_12_eq : ∀ k : Fin 16, amp9_0Expr 2 12 k = amp9_02_12 k := by decide +kernel
lemma amp9_02_13_eq : ∀ k : Fin 16, amp9_0Expr 2 13 k = amp9_02_13 k := by decide +kernel
lemma amp9_02_14_eq : ∀ k : Fin 16, amp9_0Expr 2 14 k = amp9_02_14 k := by decide +kernel
lemma amp9_02_15_eq : ∀ k : Fin 16, amp9_0Expr 2 15 k = amp9_02_15 k := by decide +kernel
lemma amp9_02_eq (i k : Fin 16) : amp9_0Expr 2 i k = amp9_02 i k := by
  fin_cases i
  · exact amp9_02_0_eq k
  · exact amp9_02_1_eq k
  · exact amp9_02_2_eq k
  · exact amp9_02_3_eq k
  · exact amp9_02_4_eq k
  · exact amp9_02_5_eq k
  · exact amp9_02_6_eq k
  · exact amp9_02_7_eq k
  · exact amp9_02_8_eq k
  · exact amp9_02_9_eq k
  · exact amp9_02_10_eq k
  · exact amp9_02_11_eq k
  · exact amp9_02_12_eq k
  · exact amp9_02_13_eq k
  · exact amp9_02_14_eq k
  · exact amp9_02_15_eq k
lemma amp9_03_0_eq : ∀ k : Fin 16, amp9_0Expr 3 0 k = amp9_03_0 k := by decide +kernel
lemma amp9_03_1_eq : ∀ k : Fin 16, amp9_0Expr 3 1 k = amp9_03_1 k := by decide +kernel
lemma amp9_03_2_eq : ∀ k : Fin 16, amp9_0Expr 3 2 k = amp9_03_2 k := by decide +kernel
lemma amp9_03_3_eq : ∀ k : Fin 16, amp9_0Expr 3 3 k = amp9_03_3 k := by decide +kernel
lemma amp9_03_4_eq : ∀ k : Fin 16, amp9_0Expr 3 4 k = amp9_03_4 k := by decide +kernel
lemma amp9_03_5_eq : ∀ k : Fin 16, amp9_0Expr 3 5 k = amp9_03_5 k := by decide +kernel
lemma amp9_03_6_eq : ∀ k : Fin 16, amp9_0Expr 3 6 k = amp9_03_6 k := by decide +kernel
lemma amp9_03_7_eq : ∀ k : Fin 16, amp9_0Expr 3 7 k = amp9_03_7 k := by decide +kernel
lemma amp9_03_8_eq : ∀ k : Fin 16, amp9_0Expr 3 8 k = amp9_03_8 k := by decide +kernel
lemma amp9_03_9_eq : ∀ k : Fin 16, amp9_0Expr 3 9 k = amp9_03_9 k := by decide +kernel
lemma amp9_03_10_eq : ∀ k : Fin 16, amp9_0Expr 3 10 k = amp9_03_10 k := by decide +kernel
lemma amp9_03_11_eq : ∀ k : Fin 16, amp9_0Expr 3 11 k = amp9_03_11 k := by decide +kernel
lemma amp9_03_12_eq : ∀ k : Fin 16, amp9_0Expr 3 12 k = amp9_03_12 k := by decide +kernel
lemma amp9_03_13_eq : ∀ k : Fin 16, amp9_0Expr 3 13 k = amp9_03_13 k := by decide +kernel
lemma amp9_03_14_eq : ∀ k : Fin 16, amp9_0Expr 3 14 k = amp9_03_14 k := by decide +kernel
lemma amp9_03_15_eq : ∀ k : Fin 16, amp9_0Expr 3 15 k = amp9_03_15 k := by decide +kernel
lemma amp9_03_eq (i k : Fin 16) : amp9_0Expr 3 i k = amp9_03 i k := by
  fin_cases i
  · exact amp9_03_0_eq k
  · exact amp9_03_1_eq k
  · exact amp9_03_2_eq k
  · exact amp9_03_3_eq k
  · exact amp9_03_4_eq k
  · exact amp9_03_5_eq k
  · exact amp9_03_6_eq k
  · exact amp9_03_7_eq k
  · exact amp9_03_8_eq k
  · exact amp9_03_9_eq k
  · exact amp9_03_10_eq k
  · exact amp9_03_11_eq k
  · exact amp9_03_12_eq k
  · exact amp9_03_13_eq k
  · exact amp9_03_14_eq k
  · exact amp9_03_15_eq k
lemma amp9_04_0_eq : ∀ k : Fin 16, amp9_0Expr 4 0 k = amp9_04_0 k := by decide +kernel
lemma amp9_04_1_eq : ∀ k : Fin 16, amp9_0Expr 4 1 k = amp9_04_1 k := by decide +kernel
lemma amp9_04_2_eq : ∀ k : Fin 16, amp9_0Expr 4 2 k = amp9_04_2 k := by decide +kernel
lemma amp9_04_3_eq : ∀ k : Fin 16, amp9_0Expr 4 3 k = amp9_04_3 k := by decide +kernel
lemma amp9_04_4_eq : ∀ k : Fin 16, amp9_0Expr 4 4 k = amp9_04_4 k := by decide +kernel
lemma amp9_04_5_eq : ∀ k : Fin 16, amp9_0Expr 4 5 k = amp9_04_5 k := by decide +kernel
lemma amp9_04_6_eq : ∀ k : Fin 16, amp9_0Expr 4 6 k = amp9_04_6 k := by decide +kernel
lemma amp9_04_7_eq : ∀ k : Fin 16, amp9_0Expr 4 7 k = amp9_04_7 k := by decide +kernel
lemma amp9_04_8_eq : ∀ k : Fin 16, amp9_0Expr 4 8 k = amp9_04_8 k := by decide +kernel
lemma amp9_04_9_eq : ∀ k : Fin 16, amp9_0Expr 4 9 k = amp9_04_9 k := by decide +kernel
lemma amp9_04_10_eq : ∀ k : Fin 16, amp9_0Expr 4 10 k = amp9_04_10 k := by decide +kernel
lemma amp9_04_11_eq : ∀ k : Fin 16, amp9_0Expr 4 11 k = amp9_04_11 k := by decide +kernel
lemma amp9_04_12_eq : ∀ k : Fin 16, amp9_0Expr 4 12 k = amp9_04_12 k := by decide +kernel
lemma amp9_04_13_eq : ∀ k : Fin 16, amp9_0Expr 4 13 k = amp9_04_13 k := by decide +kernel
lemma amp9_04_14_eq : ∀ k : Fin 16, amp9_0Expr 4 14 k = amp9_04_14 k := by decide +kernel
lemma amp9_04_15_eq : ∀ k : Fin 16, amp9_0Expr 4 15 k = amp9_04_15 k := by decide +kernel
lemma amp9_04_eq (i k : Fin 16) : amp9_0Expr 4 i k = amp9_04 i k := by
  fin_cases i
  · exact amp9_04_0_eq k
  · exact amp9_04_1_eq k
  · exact amp9_04_2_eq k
  · exact amp9_04_3_eq k
  · exact amp9_04_4_eq k
  · exact amp9_04_5_eq k
  · exact amp9_04_6_eq k
  · exact amp9_04_7_eq k
  · exact amp9_04_8_eq k
  · exact amp9_04_9_eq k
  · exact amp9_04_10_eq k
  · exact amp9_04_11_eq k
  · exact amp9_04_12_eq k
  · exact amp9_04_13_eq k
  · exact amp9_04_14_eq k
  · exact amp9_04_15_eq k
lemma amp9_05_0_eq : ∀ k : Fin 16, amp9_0Expr 5 0 k = amp9_05_0 k := by decide +kernel
lemma amp9_05_1_eq : ∀ k : Fin 16, amp9_0Expr 5 1 k = amp9_05_1 k := by decide +kernel
lemma amp9_05_2_eq : ∀ k : Fin 16, amp9_0Expr 5 2 k = amp9_05_2 k := by decide +kernel
lemma amp9_05_3_eq : ∀ k : Fin 16, amp9_0Expr 5 3 k = amp9_05_3 k := by decide +kernel
lemma amp9_05_4_eq : ∀ k : Fin 16, amp9_0Expr 5 4 k = amp9_05_4 k := by decide +kernel
lemma amp9_05_5_eq : ∀ k : Fin 16, amp9_0Expr 5 5 k = amp9_05_5 k := by decide +kernel
lemma amp9_05_6_eq : ∀ k : Fin 16, amp9_0Expr 5 6 k = amp9_05_6 k := by decide +kernel
lemma amp9_05_7_eq : ∀ k : Fin 16, amp9_0Expr 5 7 k = amp9_05_7 k := by decide +kernel
lemma amp9_05_8_eq : ∀ k : Fin 16, amp9_0Expr 5 8 k = amp9_05_8 k := by decide +kernel
lemma amp9_05_9_eq : ∀ k : Fin 16, amp9_0Expr 5 9 k = amp9_05_9 k := by decide +kernel
lemma amp9_05_10_eq : ∀ k : Fin 16, amp9_0Expr 5 10 k = amp9_05_10 k := by decide +kernel
lemma amp9_05_11_eq : ∀ k : Fin 16, amp9_0Expr 5 11 k = amp9_05_11 k := by decide +kernel
lemma amp9_05_12_eq : ∀ k : Fin 16, amp9_0Expr 5 12 k = amp9_05_12 k := by decide +kernel
lemma amp9_05_13_eq : ∀ k : Fin 16, amp9_0Expr 5 13 k = amp9_05_13 k := by decide +kernel
lemma amp9_05_14_eq : ∀ k : Fin 16, amp9_0Expr 5 14 k = amp9_05_14 k := by decide +kernel
lemma amp9_05_15_eq : ∀ k : Fin 16, amp9_0Expr 5 15 k = amp9_05_15 k := by decide +kernel
lemma amp9_05_eq (i k : Fin 16) : amp9_0Expr 5 i k = amp9_05 i k := by
  fin_cases i
  · exact amp9_05_0_eq k
  · exact amp9_05_1_eq k
  · exact amp9_05_2_eq k
  · exact amp9_05_3_eq k
  · exact amp9_05_4_eq k
  · exact amp9_05_5_eq k
  · exact amp9_05_6_eq k
  · exact amp9_05_7_eq k
  · exact amp9_05_8_eq k
  · exact amp9_05_9_eq k
  · exact amp9_05_10_eq k
  · exact amp9_05_11_eq k
  · exact amp9_05_12_eq k
  · exact amp9_05_13_eq k
  · exact amp9_05_14_eq k
  · exact amp9_05_15_eq k
lemma amp9_0_eq (j : Fin 6) (i k : Fin 16) : amp9_0Expr j i k = amp9_0 j i k := by
  fin_cases j
  · exact amp9_00_eq i k
  · exact amp9_01_eq i k
  · exact amp9_02_eq i k
  · exact amp9_03_eq i k
  · exact amp9_04_eq i k
  · exact amp9_05_eq i k
lemma amp9_0_contains (j : Fin 6) (i k : Fin 16) :
    (amp9_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude false 9 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← amp9_0_eq]
  exact CBox.contains_mul_g (rcast_contains_g (weightRows_contains_g i k))
    (waveAmplitudeBox_contains_g (gridRows_contains_g j i k) (aLookup_contains_g 9 j) (bLookup_contains_g 9 j) false)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns30
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
lemma column21_0_r0_0_eq : ∀ k : Fin 16, column21_0Expr 0 0 k = column21_0_r0_0 k := by decide +kernel
lemma column21_0_r0_1_eq : ∀ k : Fin 16, column21_0Expr 0 1 k = column21_0_r0_1 k := by decide +kernel
lemma column21_0_r0_2_eq : ∀ k : Fin 16, column21_0Expr 0 2 k = column21_0_r0_2 k := by decide +kernel
lemma column21_0_r0_3_eq : ∀ k : Fin 16, column21_0Expr 0 3 k = column21_0_r0_3 k := by decide +kernel
lemma column21_0_r0_4_eq : ∀ k : Fin 16, column21_0Expr 0 4 k = column21_0_r0_4 k := by decide +kernel
lemma column21_0_r0_5_eq : ∀ k : Fin 16, column21_0Expr 0 5 k = column21_0_r0_5 k := by decide +kernel
lemma column21_0_r0_6_eq : ∀ k : Fin 16, column21_0Expr 0 6 k = column21_0_r0_6 k := by decide +kernel
lemma column21_0_r0_7_eq : ∀ k : Fin 16, column21_0Expr 0 7 k = column21_0_r0_7 k := by decide +kernel
lemma column21_0_r0_8_eq : ∀ k : Fin 16, column21_0Expr 0 8 k = column21_0_r0_8 k := by decide +kernel
lemma column21_0_r0_9_eq : ∀ k : Fin 16, column21_0Expr 0 9 k = column21_0_r0_9 k := by decide +kernel
lemma column21_0_r0_10_eq : ∀ k : Fin 16, column21_0Expr 0 10 k = column21_0_r0_10 k := by decide +kernel
lemma column21_0_r0_11_eq : ∀ k : Fin 16, column21_0Expr 0 11 k = column21_0_r0_11 k := by decide +kernel
lemma column21_0_r0_12_eq : ∀ k : Fin 16, column21_0Expr 0 12 k = column21_0_r0_12 k := by decide +kernel
lemma column21_0_r0_13_eq : ∀ k : Fin 16, column21_0Expr 0 13 k = column21_0_r0_13 k := by decide +kernel
lemma column21_0_r0_14_eq : ∀ k : Fin 16, column21_0Expr 0 14 k = column21_0_r0_14 k := by decide +kernel
lemma column21_0_r0_15_eq : ∀ k : Fin 16, column21_0Expr 0 15 k = column21_0_r0_15 k := by decide +kernel
lemma column21_0_r0_eq (i k : Fin 16) : column21_0Expr 0 i k = column21_0_r0 i k := by
  fin_cases i
  · exact column21_0_r0_0_eq k
  · exact column21_0_r0_1_eq k
  · exact column21_0_r0_2_eq k
  · exact column21_0_r0_3_eq k
  · exact column21_0_r0_4_eq k
  · exact column21_0_r0_5_eq k
  · exact column21_0_r0_6_eq k
  · exact column21_0_r0_7_eq k
  · exact column21_0_r0_8_eq k
  · exact column21_0_r0_9_eq k
  · exact column21_0_r0_10_eq k
  · exact column21_0_r0_11_eq k
  · exact column21_0_r0_12_eq k
  · exact column21_0_r0_13_eq k
  · exact column21_0_r0_14_eq k
  · exact column21_0_r0_15_eq k
lemma column21_0_r1_0_eq : ∀ k : Fin 16, column21_0Expr 1 0 k = column21_0_r1_0 k := by decide +kernel
lemma column21_0_r1_1_eq : ∀ k : Fin 16, column21_0Expr 1 1 k = column21_0_r1_1 k := by decide +kernel
lemma column21_0_r1_2_eq : ∀ k : Fin 16, column21_0Expr 1 2 k = column21_0_r1_2 k := by decide +kernel
lemma column21_0_r1_3_eq : ∀ k : Fin 16, column21_0Expr 1 3 k = column21_0_r1_3 k := by decide +kernel
lemma column21_0_r1_4_eq : ∀ k : Fin 16, column21_0Expr 1 4 k = column21_0_r1_4 k := by decide +kernel
lemma column21_0_r1_5_eq : ∀ k : Fin 16, column21_0Expr 1 5 k = column21_0_r1_5 k := by decide +kernel
lemma column21_0_r1_6_eq : ∀ k : Fin 16, column21_0Expr 1 6 k = column21_0_r1_6 k := by decide +kernel
lemma column21_0_r1_7_eq : ∀ k : Fin 16, column21_0Expr 1 7 k = column21_0_r1_7 k := by decide +kernel
lemma column21_0_r1_8_eq : ∀ k : Fin 16, column21_0Expr 1 8 k = column21_0_r1_8 k := by decide +kernel
lemma column21_0_r1_9_eq : ∀ k : Fin 16, column21_0Expr 1 9 k = column21_0_r1_9 k := by decide +kernel
lemma column21_0_r1_10_eq : ∀ k : Fin 16, column21_0Expr 1 10 k = column21_0_r1_10 k := by decide +kernel
lemma column21_0_r1_11_eq : ∀ k : Fin 16, column21_0Expr 1 11 k = column21_0_r1_11 k := by decide +kernel
lemma column21_0_r1_12_eq : ∀ k : Fin 16, column21_0Expr 1 12 k = column21_0_r1_12 k := by decide +kernel
lemma column21_0_r1_13_eq : ∀ k : Fin 16, column21_0Expr 1 13 k = column21_0_r1_13 k := by decide +kernel
lemma column21_0_r1_14_eq : ∀ k : Fin 16, column21_0Expr 1 14 k = column21_0_r1_14 k := by decide +kernel
lemma column21_0_r1_15_eq : ∀ k : Fin 16, column21_0Expr 1 15 k = column21_0_r1_15 k := by decide +kernel
lemma column21_0_r1_eq (i k : Fin 16) : column21_0Expr 1 i k = column21_0_r1 i k := by
  fin_cases i
  · exact column21_0_r1_0_eq k
  · exact column21_0_r1_1_eq k
  · exact column21_0_r1_2_eq k
  · exact column21_0_r1_3_eq k
  · exact column21_0_r1_4_eq k
  · exact column21_0_r1_5_eq k
  · exact column21_0_r1_6_eq k
  · exact column21_0_r1_7_eq k
  · exact column21_0_r1_8_eq k
  · exact column21_0_r1_9_eq k
  · exact column21_0_r1_10_eq k
  · exact column21_0_r1_11_eq k
  · exact column21_0_r1_12_eq k
  · exact column21_0_r1_13_eq k
  · exact column21_0_r1_14_eq k
  · exact column21_0_r1_15_eq k
lemma column21_0_r2_0_eq : ∀ k : Fin 16, column21_0Expr 2 0 k = column21_0_r2_0 k := by decide +kernel
lemma column21_0_r2_1_eq : ∀ k : Fin 16, column21_0Expr 2 1 k = column21_0_r2_1 k := by decide +kernel
lemma column21_0_r2_2_eq : ∀ k : Fin 16, column21_0Expr 2 2 k = column21_0_r2_2 k := by decide +kernel
lemma column21_0_r2_3_eq : ∀ k : Fin 16, column21_0Expr 2 3 k = column21_0_r2_3 k := by decide +kernel
lemma column21_0_r2_4_eq : ∀ k : Fin 16, column21_0Expr 2 4 k = column21_0_r2_4 k := by decide +kernel
lemma column21_0_r2_5_eq : ∀ k : Fin 16, column21_0Expr 2 5 k = column21_0_r2_5 k := by decide +kernel
lemma column21_0_r2_6_eq : ∀ k : Fin 16, column21_0Expr 2 6 k = column21_0_r2_6 k := by decide +kernel
lemma column21_0_r2_7_eq : ∀ k : Fin 16, column21_0Expr 2 7 k = column21_0_r2_7 k := by decide +kernel
lemma column21_0_r2_8_eq : ∀ k : Fin 16, column21_0Expr 2 8 k = column21_0_r2_8 k := by decide +kernel
lemma column21_0_r2_9_eq : ∀ k : Fin 16, column21_0Expr 2 9 k = column21_0_r2_9 k := by decide +kernel
lemma column21_0_r2_10_eq : ∀ k : Fin 16, column21_0Expr 2 10 k = column21_0_r2_10 k := by decide +kernel
lemma column21_0_r2_11_eq : ∀ k : Fin 16, column21_0Expr 2 11 k = column21_0_r2_11 k := by decide +kernel
lemma column21_0_r2_12_eq : ∀ k : Fin 16, column21_0Expr 2 12 k = column21_0_r2_12 k := by decide +kernel
lemma column21_0_r2_13_eq : ∀ k : Fin 16, column21_0Expr 2 13 k = column21_0_r2_13 k := by decide +kernel
lemma column21_0_r2_14_eq : ∀ k : Fin 16, column21_0Expr 2 14 k = column21_0_r2_14 k := by decide +kernel
lemma column21_0_r2_15_eq : ∀ k : Fin 16, column21_0Expr 2 15 k = column21_0_r2_15 k := by decide +kernel
lemma column21_0_r2_eq (i k : Fin 16) : column21_0Expr 2 i k = column21_0_r2 i k := by
  fin_cases i
  · exact column21_0_r2_0_eq k
  · exact column21_0_r2_1_eq k
  · exact column21_0_r2_2_eq k
  · exact column21_0_r2_3_eq k
  · exact column21_0_r2_4_eq k
  · exact column21_0_r2_5_eq k
  · exact column21_0_r2_6_eq k
  · exact column21_0_r2_7_eq k
  · exact column21_0_r2_8_eq k
  · exact column21_0_r2_9_eq k
  · exact column21_0_r2_10_eq k
  · exact column21_0_r2_11_eq k
  · exact column21_0_r2_12_eq k
  · exact column21_0_r2_13_eq k
  · exact column21_0_r2_14_eq k
  · exact column21_0_r2_15_eq k
lemma column21_0_r3_0_eq : ∀ k : Fin 16, column21_0Expr 3 0 k = column21_0_r3_0 k := by decide +kernel
lemma column21_0_r3_1_eq : ∀ k : Fin 16, column21_0Expr 3 1 k = column21_0_r3_1 k := by decide +kernel
lemma column21_0_r3_2_eq : ∀ k : Fin 16, column21_0Expr 3 2 k = column21_0_r3_2 k := by decide +kernel
lemma column21_0_r3_3_eq : ∀ k : Fin 16, column21_0Expr 3 3 k = column21_0_r3_3 k := by decide +kernel
lemma column21_0_r3_4_eq : ∀ k : Fin 16, column21_0Expr 3 4 k = column21_0_r3_4 k := by decide +kernel
lemma column21_0_r3_5_eq : ∀ k : Fin 16, column21_0Expr 3 5 k = column21_0_r3_5 k := by decide +kernel
lemma column21_0_r3_6_eq : ∀ k : Fin 16, column21_0Expr 3 6 k = column21_0_r3_6 k := by decide +kernel
lemma column21_0_r3_7_eq : ∀ k : Fin 16, column21_0Expr 3 7 k = column21_0_r3_7 k := by decide +kernel
lemma column21_0_r3_8_eq : ∀ k : Fin 16, column21_0Expr 3 8 k = column21_0_r3_8 k := by decide +kernel
lemma column21_0_r3_9_eq : ∀ k : Fin 16, column21_0Expr 3 9 k = column21_0_r3_9 k := by decide +kernel
lemma column21_0_r3_10_eq : ∀ k : Fin 16, column21_0Expr 3 10 k = column21_0_r3_10 k := by decide +kernel
lemma column21_0_r3_11_eq : ∀ k : Fin 16, column21_0Expr 3 11 k = column21_0_r3_11 k := by decide +kernel
lemma column21_0_r3_12_eq : ∀ k : Fin 16, column21_0Expr 3 12 k = column21_0_r3_12 k := by decide +kernel
lemma column21_0_r3_13_eq : ∀ k : Fin 16, column21_0Expr 3 13 k = column21_0_r3_13 k := by decide +kernel
lemma column21_0_r3_14_eq : ∀ k : Fin 16, column21_0Expr 3 14 k = column21_0_r3_14 k := by decide +kernel
lemma column21_0_r3_15_eq : ∀ k : Fin 16, column21_0Expr 3 15 k = column21_0_r3_15 k := by decide +kernel
lemma column21_0_r3_eq (i k : Fin 16) : column21_0Expr 3 i k = column21_0_r3 i k := by
  fin_cases i
  · exact column21_0_r3_0_eq k
  · exact column21_0_r3_1_eq k
  · exact column21_0_r3_2_eq k
  · exact column21_0_r3_3_eq k
  · exact column21_0_r3_4_eq k
  · exact column21_0_r3_5_eq k
  · exact column21_0_r3_6_eq k
  · exact column21_0_r3_7_eq k
  · exact column21_0_r3_8_eq k
  · exact column21_0_r3_9_eq k
  · exact column21_0_r3_10_eq k
  · exact column21_0_r3_11_eq k
  · exact column21_0_r3_12_eq k
  · exact column21_0_r3_13_eq k
  · exact column21_0_r3_14_eq k
  · exact column21_0_r3_15_eq k
lemma column21_0_r4_0_eq : ∀ k : Fin 16, column21_0Expr 4 0 k = column21_0_r4_0 k := by decide +kernel
lemma column21_0_r4_1_eq : ∀ k : Fin 16, column21_0Expr 4 1 k = column21_0_r4_1 k := by decide +kernel
lemma column21_0_r4_2_eq : ∀ k : Fin 16, column21_0Expr 4 2 k = column21_0_r4_2 k := by decide +kernel
lemma column21_0_r4_3_eq : ∀ k : Fin 16, column21_0Expr 4 3 k = column21_0_r4_3 k := by decide +kernel
lemma column21_0_r4_4_eq : ∀ k : Fin 16, column21_0Expr 4 4 k = column21_0_r4_4 k := by decide +kernel
lemma column21_0_r4_5_eq : ∀ k : Fin 16, column21_0Expr 4 5 k = column21_0_r4_5 k := by decide +kernel
lemma column21_0_r4_6_eq : ∀ k : Fin 16, column21_0Expr 4 6 k = column21_0_r4_6 k := by decide +kernel
lemma column21_0_r4_7_eq : ∀ k : Fin 16, column21_0Expr 4 7 k = column21_0_r4_7 k := by decide +kernel
lemma column21_0_r4_8_eq : ∀ k : Fin 16, column21_0Expr 4 8 k = column21_0_r4_8 k := by decide +kernel
lemma column21_0_r4_9_eq : ∀ k : Fin 16, column21_0Expr 4 9 k = column21_0_r4_9 k := by decide +kernel
lemma column21_0_r4_10_eq : ∀ k : Fin 16, column21_0Expr 4 10 k = column21_0_r4_10 k := by decide +kernel
lemma column21_0_r4_11_eq : ∀ k : Fin 16, column21_0Expr 4 11 k = column21_0_r4_11 k := by decide +kernel
lemma column21_0_r4_12_eq : ∀ k : Fin 16, column21_0Expr 4 12 k = column21_0_r4_12 k := by decide +kernel
lemma column21_0_r4_13_eq : ∀ k : Fin 16, column21_0Expr 4 13 k = column21_0_r4_13 k := by decide +kernel
lemma column21_0_r4_14_eq : ∀ k : Fin 16, column21_0Expr 4 14 k = column21_0_r4_14 k := by decide +kernel
lemma column21_0_r4_15_eq : ∀ k : Fin 16, column21_0Expr 4 15 k = column21_0_r4_15 k := by decide +kernel
lemma column21_0_r4_eq (i k : Fin 16) : column21_0Expr 4 i k = column21_0_r4 i k := by
  fin_cases i
  · exact column21_0_r4_0_eq k
  · exact column21_0_r4_1_eq k
  · exact column21_0_r4_2_eq k
  · exact column21_0_r4_3_eq k
  · exact column21_0_r4_4_eq k
  · exact column21_0_r4_5_eq k
  · exact column21_0_r4_6_eq k
  · exact column21_0_r4_7_eq k
  · exact column21_0_r4_8_eq k
  · exact column21_0_r4_9_eq k
  · exact column21_0_r4_10_eq k
  · exact column21_0_r4_11_eq k
  · exact column21_0_r4_12_eq k
  · exact column21_0_r4_13_eq k
  · exact column21_0_r4_14_eq k
  · exact column21_0_r4_15_eq k
lemma column21_0_r5_0_eq : ∀ k : Fin 16, column21_0Expr 5 0 k = column21_0_r5_0 k := by decide +kernel
lemma column21_0_r5_1_eq : ∀ k : Fin 16, column21_0Expr 5 1 k = column21_0_r5_1 k := by decide +kernel
lemma column21_0_r5_2_eq : ∀ k : Fin 16, column21_0Expr 5 2 k = column21_0_r5_2 k := by decide +kernel
lemma column21_0_r5_3_eq : ∀ k : Fin 16, column21_0Expr 5 3 k = column21_0_r5_3 k := by decide +kernel
lemma column21_0_r5_4_eq : ∀ k : Fin 16, column21_0Expr 5 4 k = column21_0_r5_4 k := by decide +kernel
lemma column21_0_r5_5_eq : ∀ k : Fin 16, column21_0Expr 5 5 k = column21_0_r5_5 k := by decide +kernel
lemma column21_0_r5_6_eq : ∀ k : Fin 16, column21_0Expr 5 6 k = column21_0_r5_6 k := by decide +kernel
lemma column21_0_r5_7_eq : ∀ k : Fin 16, column21_0Expr 5 7 k = column21_0_r5_7 k := by decide +kernel
lemma column21_0_r5_8_eq : ∀ k : Fin 16, column21_0Expr 5 8 k = column21_0_r5_8 k := by decide +kernel
lemma column21_0_r5_9_eq : ∀ k : Fin 16, column21_0Expr 5 9 k = column21_0_r5_9 k := by decide +kernel
lemma column21_0_r5_10_eq : ∀ k : Fin 16, column21_0Expr 5 10 k = column21_0_r5_10 k := by decide +kernel
lemma column21_0_r5_11_eq : ∀ k : Fin 16, column21_0Expr 5 11 k = column21_0_r5_11 k := by decide +kernel
lemma column21_0_r5_12_eq : ∀ k : Fin 16, column21_0Expr 5 12 k = column21_0_r5_12 k := by decide +kernel
lemma column21_0_r5_13_eq : ∀ k : Fin 16, column21_0Expr 5 13 k = column21_0_r5_13 k := by decide +kernel
lemma column21_0_r5_14_eq : ∀ k : Fin 16, column21_0Expr 5 14 k = column21_0_r5_14 k := by decide +kernel
lemma column21_0_r5_15_eq : ∀ k : Fin 16, column21_0Expr 5 15 k = column21_0_r5_15 k := by decide +kernel
lemma column21_0_r5_eq (i k : Fin 16) : column21_0Expr 5 i k = column21_0_r5 i k := by
  fin_cases i
  · exact column21_0_r5_0_eq k
  · exact column21_0_r5_1_eq k
  · exact column21_0_r5_2_eq k
  · exact column21_0_r5_3_eq k
  · exact column21_0_r5_4_eq k
  · exact column21_0_r5_5_eq k
  · exact column21_0_r5_6_eq k
  · exact column21_0_r5_7_eq k
  · exact column21_0_r5_8_eq k
  · exact column21_0_r5_9_eq k
  · exact column21_0_r5_10_eq k
  · exact column21_0_r5_11_eq k
  · exact column21_0_r5_12_eq k
  · exact column21_0_r5_13_eq k
  · exact column21_0_r5_14_eq k
  · exact column21_0_r5_15_eq k
lemma column21_0_eq (j : Fin 6) (i k : Fin 16) : column21_0Expr j i k = column21_0 j i k := by
  fin_cases j
  · exact column21_0_r0_eq i k
  · exact column21_0_r1_eq i k
  · exact column21_0_r2_eq i k
  · exact column21_0_r3_eq i k
  · exact column21_0_r4_eq i k
  · exact column21_0_r5_eq i k
lemma column21_0_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (column21_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 21 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column21_0_eq,basisFunction_wave_g,← mul_assoc]
  unfold column21_0Expr
  apply CBox.contains_mul_g
  · rw [← waveAmplitude_mod false 21 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp9_0_contains j i k
  · exact power21_contains_g j i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.column21_0_contains_g_oai := @OAI.SharpPlanar.CachedData.column21_0_contains_g_oai
