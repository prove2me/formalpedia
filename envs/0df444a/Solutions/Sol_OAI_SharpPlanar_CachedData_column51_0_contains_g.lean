-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.column51_0_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:13:33.719811+00:00
-- url     : https://prove2.me/submissions/40dbe5d5-dca3-4ae1-a6b0-e59359fca03f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G176
import Definitions.Def_OAIQ098G263
import Definitions.Def_OAIQ098G328
import Theorems.Thm_OAI_SharpPlanar_CachedData_power50_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aLookup_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bLookup_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisAlpha_mod_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisBeta_mod_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisFunction_wave_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_exp_direct_step_g
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
lemma amp3_00_0_eq : ∀ k : Fin 16, amp3_0Expr 0 0 k = amp3_00_0 k := by decide +kernel
lemma amp3_00_1_eq : ∀ k : Fin 16, amp3_0Expr 0 1 k = amp3_00_1 k := by decide +kernel
lemma amp3_00_2_eq : ∀ k : Fin 16, amp3_0Expr 0 2 k = amp3_00_2 k := by decide +kernel
lemma amp3_00_3_eq : ∀ k : Fin 16, amp3_0Expr 0 3 k = amp3_00_3 k := by decide +kernel
lemma amp3_00_4_eq : ∀ k : Fin 16, amp3_0Expr 0 4 k = amp3_00_4 k := by decide +kernel
lemma amp3_00_5_eq : ∀ k : Fin 16, amp3_0Expr 0 5 k = amp3_00_5 k := by decide +kernel
lemma amp3_00_6_eq : ∀ k : Fin 16, amp3_0Expr 0 6 k = amp3_00_6 k := by decide +kernel
lemma amp3_00_7_eq : ∀ k : Fin 16, amp3_0Expr 0 7 k = amp3_00_7 k := by decide +kernel
lemma amp3_00_8_eq : ∀ k : Fin 16, amp3_0Expr 0 8 k = amp3_00_8 k := by decide +kernel
lemma amp3_00_9_eq : ∀ k : Fin 16, amp3_0Expr 0 9 k = amp3_00_9 k := by decide +kernel
lemma amp3_00_10_eq : ∀ k : Fin 16, amp3_0Expr 0 10 k = amp3_00_10 k := by decide +kernel
lemma amp3_00_11_eq : ∀ k : Fin 16, amp3_0Expr 0 11 k = amp3_00_11 k := by decide +kernel
lemma amp3_00_12_eq : ∀ k : Fin 16, amp3_0Expr 0 12 k = amp3_00_12 k := by decide +kernel
lemma amp3_00_13_eq : ∀ k : Fin 16, amp3_0Expr 0 13 k = amp3_00_13 k := by decide +kernel
lemma amp3_00_14_eq : ∀ k : Fin 16, amp3_0Expr 0 14 k = amp3_00_14 k := by decide +kernel
lemma amp3_00_15_eq : ∀ k : Fin 16, amp3_0Expr 0 15 k = amp3_00_15 k := by decide +kernel
lemma amp3_00_eq (i k : Fin 16) : amp3_0Expr 0 i k = amp3_00 i k := by
  fin_cases i
  · exact amp3_00_0_eq k
  · exact amp3_00_1_eq k
  · exact amp3_00_2_eq k
  · exact amp3_00_3_eq k
  · exact amp3_00_4_eq k
  · exact amp3_00_5_eq k
  · exact amp3_00_6_eq k
  · exact amp3_00_7_eq k
  · exact amp3_00_8_eq k
  · exact amp3_00_9_eq k
  · exact amp3_00_10_eq k
  · exact amp3_00_11_eq k
  · exact amp3_00_12_eq k
  · exact amp3_00_13_eq k
  · exact amp3_00_14_eq k
  · exact amp3_00_15_eq k
lemma amp3_01_0_eq : ∀ k : Fin 16, amp3_0Expr 1 0 k = amp3_01_0 k := by decide +kernel
lemma amp3_01_1_eq : ∀ k : Fin 16, amp3_0Expr 1 1 k = amp3_01_1 k := by decide +kernel
lemma amp3_01_2_eq : ∀ k : Fin 16, amp3_0Expr 1 2 k = amp3_01_2 k := by decide +kernel
lemma amp3_01_3_eq : ∀ k : Fin 16, amp3_0Expr 1 3 k = amp3_01_3 k := by decide +kernel
lemma amp3_01_4_eq : ∀ k : Fin 16, amp3_0Expr 1 4 k = amp3_01_4 k := by decide +kernel
lemma amp3_01_5_eq : ∀ k : Fin 16, amp3_0Expr 1 5 k = amp3_01_5 k := by decide +kernel
lemma amp3_01_6_eq : ∀ k : Fin 16, amp3_0Expr 1 6 k = amp3_01_6 k := by decide +kernel
lemma amp3_01_7_eq : ∀ k : Fin 16, amp3_0Expr 1 7 k = amp3_01_7 k := by decide +kernel
lemma amp3_01_8_eq : ∀ k : Fin 16, amp3_0Expr 1 8 k = amp3_01_8 k := by decide +kernel
lemma amp3_01_9_eq : ∀ k : Fin 16, amp3_0Expr 1 9 k = amp3_01_9 k := by decide +kernel
lemma amp3_01_10_eq : ∀ k : Fin 16, amp3_0Expr 1 10 k = amp3_01_10 k := by decide +kernel
lemma amp3_01_11_eq : ∀ k : Fin 16, amp3_0Expr 1 11 k = amp3_01_11 k := by decide +kernel
lemma amp3_01_12_eq : ∀ k : Fin 16, amp3_0Expr 1 12 k = amp3_01_12 k := by decide +kernel
lemma amp3_01_13_eq : ∀ k : Fin 16, amp3_0Expr 1 13 k = amp3_01_13 k := by decide +kernel
lemma amp3_01_14_eq : ∀ k : Fin 16, amp3_0Expr 1 14 k = amp3_01_14 k := by decide +kernel
lemma amp3_01_15_eq : ∀ k : Fin 16, amp3_0Expr 1 15 k = amp3_01_15 k := by decide +kernel
lemma amp3_01_eq (i k : Fin 16) : amp3_0Expr 1 i k = amp3_01 i k := by
  fin_cases i
  · exact amp3_01_0_eq k
  · exact amp3_01_1_eq k
  · exact amp3_01_2_eq k
  · exact amp3_01_3_eq k
  · exact amp3_01_4_eq k
  · exact amp3_01_5_eq k
  · exact amp3_01_6_eq k
  · exact amp3_01_7_eq k
  · exact amp3_01_8_eq k
  · exact amp3_01_9_eq k
  · exact amp3_01_10_eq k
  · exact amp3_01_11_eq k
  · exact amp3_01_12_eq k
  · exact amp3_01_13_eq k
  · exact amp3_01_14_eq k
  · exact amp3_01_15_eq k
lemma amp3_02_0_eq : ∀ k : Fin 16, amp3_0Expr 2 0 k = amp3_02_0 k := by decide +kernel
lemma amp3_02_1_eq : ∀ k : Fin 16, amp3_0Expr 2 1 k = amp3_02_1 k := by decide +kernel
lemma amp3_02_2_eq : ∀ k : Fin 16, amp3_0Expr 2 2 k = amp3_02_2 k := by decide +kernel
lemma amp3_02_3_eq : ∀ k : Fin 16, amp3_0Expr 2 3 k = amp3_02_3 k := by decide +kernel
lemma amp3_02_4_eq : ∀ k : Fin 16, amp3_0Expr 2 4 k = amp3_02_4 k := by decide +kernel
lemma amp3_02_5_eq : ∀ k : Fin 16, amp3_0Expr 2 5 k = amp3_02_5 k := by decide +kernel
lemma amp3_02_6_eq : ∀ k : Fin 16, amp3_0Expr 2 6 k = amp3_02_6 k := by decide +kernel
lemma amp3_02_7_eq : ∀ k : Fin 16, amp3_0Expr 2 7 k = amp3_02_7 k := by decide +kernel
lemma amp3_02_8_eq : ∀ k : Fin 16, amp3_0Expr 2 8 k = amp3_02_8 k := by decide +kernel
lemma amp3_02_9_eq : ∀ k : Fin 16, amp3_0Expr 2 9 k = amp3_02_9 k := by decide +kernel
lemma amp3_02_10_eq : ∀ k : Fin 16, amp3_0Expr 2 10 k = amp3_02_10 k := by decide +kernel
lemma amp3_02_11_eq : ∀ k : Fin 16, amp3_0Expr 2 11 k = amp3_02_11 k := by decide +kernel
lemma amp3_02_12_eq : ∀ k : Fin 16, amp3_0Expr 2 12 k = amp3_02_12 k := by decide +kernel
lemma amp3_02_13_eq : ∀ k : Fin 16, amp3_0Expr 2 13 k = amp3_02_13 k := by decide +kernel
lemma amp3_02_14_eq : ∀ k : Fin 16, amp3_0Expr 2 14 k = amp3_02_14 k := by decide +kernel
lemma amp3_02_15_eq : ∀ k : Fin 16, amp3_0Expr 2 15 k = amp3_02_15 k := by decide +kernel
lemma amp3_02_eq (i k : Fin 16) : amp3_0Expr 2 i k = amp3_02 i k := by
  fin_cases i
  · exact amp3_02_0_eq k
  · exact amp3_02_1_eq k
  · exact amp3_02_2_eq k
  · exact amp3_02_3_eq k
  · exact amp3_02_4_eq k
  · exact amp3_02_5_eq k
  · exact amp3_02_6_eq k
  · exact amp3_02_7_eq k
  · exact amp3_02_8_eq k
  · exact amp3_02_9_eq k
  · exact amp3_02_10_eq k
  · exact amp3_02_11_eq k
  · exact amp3_02_12_eq k
  · exact amp3_02_13_eq k
  · exact amp3_02_14_eq k
  · exact amp3_02_15_eq k
lemma amp3_03_0_eq : ∀ k : Fin 16, amp3_0Expr 3 0 k = amp3_03_0 k := by decide +kernel
lemma amp3_03_1_eq : ∀ k : Fin 16, amp3_0Expr 3 1 k = amp3_03_1 k := by decide +kernel
lemma amp3_03_2_eq : ∀ k : Fin 16, amp3_0Expr 3 2 k = amp3_03_2 k := by decide +kernel
lemma amp3_03_3_eq : ∀ k : Fin 16, amp3_0Expr 3 3 k = amp3_03_3 k := by decide +kernel
lemma amp3_03_4_eq : ∀ k : Fin 16, amp3_0Expr 3 4 k = amp3_03_4 k := by decide +kernel
lemma amp3_03_5_eq : ∀ k : Fin 16, amp3_0Expr 3 5 k = amp3_03_5 k := by decide +kernel
lemma amp3_03_6_eq : ∀ k : Fin 16, amp3_0Expr 3 6 k = amp3_03_6 k := by decide +kernel
lemma amp3_03_7_eq : ∀ k : Fin 16, amp3_0Expr 3 7 k = amp3_03_7 k := by decide +kernel
lemma amp3_03_8_eq : ∀ k : Fin 16, amp3_0Expr 3 8 k = amp3_03_8 k := by decide +kernel
lemma amp3_03_9_eq : ∀ k : Fin 16, amp3_0Expr 3 9 k = amp3_03_9 k := by decide +kernel
lemma amp3_03_10_eq : ∀ k : Fin 16, amp3_0Expr 3 10 k = amp3_03_10 k := by decide +kernel
lemma amp3_03_11_eq : ∀ k : Fin 16, amp3_0Expr 3 11 k = amp3_03_11 k := by decide +kernel
lemma amp3_03_12_eq : ∀ k : Fin 16, amp3_0Expr 3 12 k = amp3_03_12 k := by decide +kernel
lemma amp3_03_13_eq : ∀ k : Fin 16, amp3_0Expr 3 13 k = amp3_03_13 k := by decide +kernel
lemma amp3_03_14_eq : ∀ k : Fin 16, amp3_0Expr 3 14 k = amp3_03_14 k := by decide +kernel
lemma amp3_03_15_eq : ∀ k : Fin 16, amp3_0Expr 3 15 k = amp3_03_15 k := by decide +kernel
lemma amp3_03_eq (i k : Fin 16) : amp3_0Expr 3 i k = amp3_03 i k := by
  fin_cases i
  · exact amp3_03_0_eq k
  · exact amp3_03_1_eq k
  · exact amp3_03_2_eq k
  · exact amp3_03_3_eq k
  · exact amp3_03_4_eq k
  · exact amp3_03_5_eq k
  · exact amp3_03_6_eq k
  · exact amp3_03_7_eq k
  · exact amp3_03_8_eq k
  · exact amp3_03_9_eq k
  · exact amp3_03_10_eq k
  · exact amp3_03_11_eq k
  · exact amp3_03_12_eq k
  · exact amp3_03_13_eq k
  · exact amp3_03_14_eq k
  · exact amp3_03_15_eq k
lemma amp3_04_0_eq : ∀ k : Fin 16, amp3_0Expr 4 0 k = amp3_04_0 k := by decide +kernel
lemma amp3_04_1_eq : ∀ k : Fin 16, amp3_0Expr 4 1 k = amp3_04_1 k := by decide +kernel
lemma amp3_04_2_eq : ∀ k : Fin 16, amp3_0Expr 4 2 k = amp3_04_2 k := by decide +kernel
lemma amp3_04_3_eq : ∀ k : Fin 16, amp3_0Expr 4 3 k = amp3_04_3 k := by decide +kernel
lemma amp3_04_4_eq : ∀ k : Fin 16, amp3_0Expr 4 4 k = amp3_04_4 k := by decide +kernel
lemma amp3_04_5_eq : ∀ k : Fin 16, amp3_0Expr 4 5 k = amp3_04_5 k := by decide +kernel
lemma amp3_04_6_eq : ∀ k : Fin 16, amp3_0Expr 4 6 k = amp3_04_6 k := by decide +kernel
lemma amp3_04_7_eq : ∀ k : Fin 16, amp3_0Expr 4 7 k = amp3_04_7 k := by decide +kernel
lemma amp3_04_8_eq : ∀ k : Fin 16, amp3_0Expr 4 8 k = amp3_04_8 k := by decide +kernel
lemma amp3_04_9_eq : ∀ k : Fin 16, amp3_0Expr 4 9 k = amp3_04_9 k := by decide +kernel
lemma amp3_04_10_eq : ∀ k : Fin 16, amp3_0Expr 4 10 k = amp3_04_10 k := by decide +kernel
lemma amp3_04_11_eq : ∀ k : Fin 16, amp3_0Expr 4 11 k = amp3_04_11 k := by decide +kernel
lemma amp3_04_12_eq : ∀ k : Fin 16, amp3_0Expr 4 12 k = amp3_04_12 k := by decide +kernel
lemma amp3_04_13_eq : ∀ k : Fin 16, amp3_0Expr 4 13 k = amp3_04_13 k := by decide +kernel
lemma amp3_04_14_eq : ∀ k : Fin 16, amp3_0Expr 4 14 k = amp3_04_14 k := by decide +kernel
lemma amp3_04_15_eq : ∀ k : Fin 16, amp3_0Expr 4 15 k = amp3_04_15 k := by decide +kernel
lemma amp3_04_eq (i k : Fin 16) : amp3_0Expr 4 i k = amp3_04 i k := by
  fin_cases i
  · exact amp3_04_0_eq k
  · exact amp3_04_1_eq k
  · exact amp3_04_2_eq k
  · exact amp3_04_3_eq k
  · exact amp3_04_4_eq k
  · exact amp3_04_5_eq k
  · exact amp3_04_6_eq k
  · exact amp3_04_7_eq k
  · exact amp3_04_8_eq k
  · exact amp3_04_9_eq k
  · exact amp3_04_10_eq k
  · exact amp3_04_11_eq k
  · exact amp3_04_12_eq k
  · exact amp3_04_13_eq k
  · exact amp3_04_14_eq k
  · exact amp3_04_15_eq k
lemma amp3_05_0_eq : ∀ k : Fin 16, amp3_0Expr 5 0 k = amp3_05_0 k := by decide +kernel
lemma amp3_05_1_eq : ∀ k : Fin 16, amp3_0Expr 5 1 k = amp3_05_1 k := by decide +kernel
lemma amp3_05_2_eq : ∀ k : Fin 16, amp3_0Expr 5 2 k = amp3_05_2 k := by decide +kernel
lemma amp3_05_3_eq : ∀ k : Fin 16, amp3_0Expr 5 3 k = amp3_05_3 k := by decide +kernel
lemma amp3_05_4_eq : ∀ k : Fin 16, amp3_0Expr 5 4 k = amp3_05_4 k := by decide +kernel
lemma amp3_05_5_eq : ∀ k : Fin 16, amp3_0Expr 5 5 k = amp3_05_5 k := by decide +kernel
lemma amp3_05_6_eq : ∀ k : Fin 16, amp3_0Expr 5 6 k = amp3_05_6 k := by decide +kernel
lemma amp3_05_7_eq : ∀ k : Fin 16, amp3_0Expr 5 7 k = amp3_05_7 k := by decide +kernel
lemma amp3_05_8_eq : ∀ k : Fin 16, amp3_0Expr 5 8 k = amp3_05_8 k := by decide +kernel
lemma amp3_05_9_eq : ∀ k : Fin 16, amp3_0Expr 5 9 k = amp3_05_9 k := by decide +kernel
lemma amp3_05_10_eq : ∀ k : Fin 16, amp3_0Expr 5 10 k = amp3_05_10 k := by decide +kernel
lemma amp3_05_11_eq : ∀ k : Fin 16, amp3_0Expr 5 11 k = amp3_05_11 k := by decide +kernel
lemma amp3_05_12_eq : ∀ k : Fin 16, amp3_0Expr 5 12 k = amp3_05_12 k := by decide +kernel
lemma amp3_05_13_eq : ∀ k : Fin 16, amp3_0Expr 5 13 k = amp3_05_13 k := by decide +kernel
lemma amp3_05_14_eq : ∀ k : Fin 16, amp3_0Expr 5 14 k = amp3_05_14 k := by decide +kernel
lemma amp3_05_15_eq : ∀ k : Fin 16, amp3_0Expr 5 15 k = amp3_05_15 k := by decide +kernel
lemma amp3_05_eq (i k : Fin 16) : amp3_0Expr 5 i k = amp3_05 i k := by
  fin_cases i
  · exact amp3_05_0_eq k
  · exact amp3_05_1_eq k
  · exact amp3_05_2_eq k
  · exact amp3_05_3_eq k
  · exact amp3_05_4_eq k
  · exact amp3_05_5_eq k
  · exact amp3_05_6_eq k
  · exact amp3_05_7_eq k
  · exact amp3_05_8_eq k
  · exact amp3_05_9_eq k
  · exact amp3_05_10_eq k
  · exact amp3_05_11_eq k
  · exact amp3_05_12_eq k
  · exact amp3_05_13_eq k
  · exact amp3_05_14_eq k
  · exact amp3_05_15_eq k
lemma amp3_0_eq (j : Fin 6) (i k : Fin 16) : amp3_0Expr j i k = amp3_0 j i k := by
  fin_cases j
  · exact amp3_00_eq i k
  · exact amp3_01_eq i k
  · exact amp3_02_eq i k
  · exact amp3_03_eq i k
  · exact amp3_04_eq i k
  · exact amp3_05_eq i k
lemma amp3_0_contains (j : Fin 6) (i k : Fin 16) :
    (amp3_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude false 3 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← amp3_0_eq]
  exact CBox.contains_mul_g (rcast_contains_g (weightRows_contains_g i k))
    (waveAmplitudeBox_contains_g (gridRows_contains_g j i k) (aLookup_contains_g 3 j) (bLookup_contains_g 3 j) false)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers60
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
lemma power51_r0_0_eq : ∀ k : Fin 16, power51Expr 0 0 k = power51_r0_0 k := by decide +kernel
lemma power51_r0_1_eq : ∀ k : Fin 16, power51Expr 0 1 k = power51_r0_1 k := by decide +kernel
lemma power51_r0_2_eq : ∀ k : Fin 16, power51Expr 0 2 k = power51_r0_2 k := by decide +kernel
lemma power51_r0_3_eq : ∀ k : Fin 16, power51Expr 0 3 k = power51_r0_3 k := by decide +kernel
lemma power51_r0_4_eq : ∀ k : Fin 16, power51Expr 0 4 k = power51_r0_4 k := by decide +kernel
lemma power51_r0_5_eq : ∀ k : Fin 16, power51Expr 0 5 k = power51_r0_5 k := by decide +kernel
lemma power51_r0_6_eq : ∀ k : Fin 16, power51Expr 0 6 k = power51_r0_6 k := by decide +kernel
lemma power51_r0_7_eq : ∀ k : Fin 16, power51Expr 0 7 k = power51_r0_7 k := by decide +kernel
lemma power51_r0_8_eq : ∀ k : Fin 16, power51Expr 0 8 k = power51_r0_8 k := by decide +kernel
lemma power51_r0_9_eq : ∀ k : Fin 16, power51Expr 0 9 k = power51_r0_9 k := by decide +kernel
lemma power51_r0_10_eq : ∀ k : Fin 16, power51Expr 0 10 k = power51_r0_10 k := by decide +kernel
lemma power51_r0_11_eq : ∀ k : Fin 16, power51Expr 0 11 k = power51_r0_11 k := by decide +kernel
lemma power51_r0_12_eq : ∀ k : Fin 16, power51Expr 0 12 k = power51_r0_12 k := by decide +kernel
lemma power51_r0_13_eq : ∀ k : Fin 16, power51Expr 0 13 k = power51_r0_13 k := by decide +kernel
lemma power51_r0_14_eq : ∀ k : Fin 16, power51Expr 0 14 k = power51_r0_14 k := by decide +kernel
lemma power51_r0_15_eq : ∀ k : Fin 16, power51Expr 0 15 k = power51_r0_15 k := by decide +kernel
lemma power51_r0_eq (i k : Fin 16) : power51Expr 0 i k = power51_r0 i k := by
  fin_cases i
  · exact power51_r0_0_eq k
  · exact power51_r0_1_eq k
  · exact power51_r0_2_eq k
  · exact power51_r0_3_eq k
  · exact power51_r0_4_eq k
  · exact power51_r0_5_eq k
  · exact power51_r0_6_eq k
  · exact power51_r0_7_eq k
  · exact power51_r0_8_eq k
  · exact power51_r0_9_eq k
  · exact power51_r0_10_eq k
  · exact power51_r0_11_eq k
  · exact power51_r0_12_eq k
  · exact power51_r0_13_eq k
  · exact power51_r0_14_eq k
  · exact power51_r0_15_eq k
lemma power51_r1_0_eq : ∀ k : Fin 16, power51Expr 1 0 k = power51_r1_0 k := by decide +kernel
lemma power51_r1_1_eq : ∀ k : Fin 16, power51Expr 1 1 k = power51_r1_1 k := by decide +kernel
lemma power51_r1_2_eq : ∀ k : Fin 16, power51Expr 1 2 k = power51_r1_2 k := by decide +kernel
lemma power51_r1_3_eq : ∀ k : Fin 16, power51Expr 1 3 k = power51_r1_3 k := by decide +kernel
lemma power51_r1_4_eq : ∀ k : Fin 16, power51Expr 1 4 k = power51_r1_4 k := by decide +kernel
lemma power51_r1_5_eq : ∀ k : Fin 16, power51Expr 1 5 k = power51_r1_5 k := by decide +kernel
lemma power51_r1_6_eq : ∀ k : Fin 16, power51Expr 1 6 k = power51_r1_6 k := by decide +kernel
lemma power51_r1_7_eq : ∀ k : Fin 16, power51Expr 1 7 k = power51_r1_7 k := by decide +kernel
lemma power51_r1_8_eq : ∀ k : Fin 16, power51Expr 1 8 k = power51_r1_8 k := by decide +kernel
lemma power51_r1_9_eq : ∀ k : Fin 16, power51Expr 1 9 k = power51_r1_9 k := by decide +kernel
lemma power51_r1_10_eq : ∀ k : Fin 16, power51Expr 1 10 k = power51_r1_10 k := by decide +kernel
lemma power51_r1_11_eq : ∀ k : Fin 16, power51Expr 1 11 k = power51_r1_11 k := by decide +kernel
lemma power51_r1_12_eq : ∀ k : Fin 16, power51Expr 1 12 k = power51_r1_12 k := by decide +kernel
lemma power51_r1_13_eq : ∀ k : Fin 16, power51Expr 1 13 k = power51_r1_13 k := by decide +kernel
lemma power51_r1_14_eq : ∀ k : Fin 16, power51Expr 1 14 k = power51_r1_14 k := by decide +kernel
lemma power51_r1_15_eq : ∀ k : Fin 16, power51Expr 1 15 k = power51_r1_15 k := by decide +kernel
lemma power51_r1_eq (i k : Fin 16) : power51Expr 1 i k = power51_r1 i k := by
  fin_cases i
  · exact power51_r1_0_eq k
  · exact power51_r1_1_eq k
  · exact power51_r1_2_eq k
  · exact power51_r1_3_eq k
  · exact power51_r1_4_eq k
  · exact power51_r1_5_eq k
  · exact power51_r1_6_eq k
  · exact power51_r1_7_eq k
  · exact power51_r1_8_eq k
  · exact power51_r1_9_eq k
  · exact power51_r1_10_eq k
  · exact power51_r1_11_eq k
  · exact power51_r1_12_eq k
  · exact power51_r1_13_eq k
  · exact power51_r1_14_eq k
  · exact power51_r1_15_eq k
lemma power51_r2_0_eq : ∀ k : Fin 16, power51Expr 2 0 k = power51_r2_0 k := by decide +kernel
lemma power51_r2_1_eq : ∀ k : Fin 16, power51Expr 2 1 k = power51_r2_1 k := by decide +kernel
lemma power51_r2_2_eq : ∀ k : Fin 16, power51Expr 2 2 k = power51_r2_2 k := by decide +kernel
lemma power51_r2_3_eq : ∀ k : Fin 16, power51Expr 2 3 k = power51_r2_3 k := by decide +kernel
lemma power51_r2_4_eq : ∀ k : Fin 16, power51Expr 2 4 k = power51_r2_4 k := by decide +kernel
lemma power51_r2_5_eq : ∀ k : Fin 16, power51Expr 2 5 k = power51_r2_5 k := by decide +kernel
lemma power51_r2_6_eq : ∀ k : Fin 16, power51Expr 2 6 k = power51_r2_6 k := by decide +kernel
lemma power51_r2_7_eq : ∀ k : Fin 16, power51Expr 2 7 k = power51_r2_7 k := by decide +kernel
lemma power51_r2_8_eq : ∀ k : Fin 16, power51Expr 2 8 k = power51_r2_8 k := by decide +kernel
lemma power51_r2_9_eq : ∀ k : Fin 16, power51Expr 2 9 k = power51_r2_9 k := by decide +kernel
lemma power51_r2_10_eq : ∀ k : Fin 16, power51Expr 2 10 k = power51_r2_10 k := by decide +kernel
lemma power51_r2_11_eq : ∀ k : Fin 16, power51Expr 2 11 k = power51_r2_11 k := by decide +kernel
lemma power51_r2_12_eq : ∀ k : Fin 16, power51Expr 2 12 k = power51_r2_12 k := by decide +kernel
lemma power51_r2_13_eq : ∀ k : Fin 16, power51Expr 2 13 k = power51_r2_13 k := by decide +kernel
lemma power51_r2_14_eq : ∀ k : Fin 16, power51Expr 2 14 k = power51_r2_14 k := by decide +kernel
lemma power51_r2_15_eq : ∀ k : Fin 16, power51Expr 2 15 k = power51_r2_15 k := by decide +kernel
lemma power51_r2_eq (i k : Fin 16) : power51Expr 2 i k = power51_r2 i k := by
  fin_cases i
  · exact power51_r2_0_eq k
  · exact power51_r2_1_eq k
  · exact power51_r2_2_eq k
  · exact power51_r2_3_eq k
  · exact power51_r2_4_eq k
  · exact power51_r2_5_eq k
  · exact power51_r2_6_eq k
  · exact power51_r2_7_eq k
  · exact power51_r2_8_eq k
  · exact power51_r2_9_eq k
  · exact power51_r2_10_eq k
  · exact power51_r2_11_eq k
  · exact power51_r2_12_eq k
  · exact power51_r2_13_eq k
  · exact power51_r2_14_eq k
  · exact power51_r2_15_eq k
lemma power51_r3_0_eq : ∀ k : Fin 16, power51Expr 3 0 k = power51_r3_0 k := by decide +kernel
lemma power51_r3_1_eq : ∀ k : Fin 16, power51Expr 3 1 k = power51_r3_1 k := by decide +kernel
lemma power51_r3_2_eq : ∀ k : Fin 16, power51Expr 3 2 k = power51_r3_2 k := by decide +kernel
lemma power51_r3_3_eq : ∀ k : Fin 16, power51Expr 3 3 k = power51_r3_3 k := by decide +kernel
lemma power51_r3_4_eq : ∀ k : Fin 16, power51Expr 3 4 k = power51_r3_4 k := by decide +kernel
lemma power51_r3_5_eq : ∀ k : Fin 16, power51Expr 3 5 k = power51_r3_5 k := by decide +kernel
lemma power51_r3_6_eq : ∀ k : Fin 16, power51Expr 3 6 k = power51_r3_6 k := by decide +kernel
lemma power51_r3_7_eq : ∀ k : Fin 16, power51Expr 3 7 k = power51_r3_7 k := by decide +kernel
lemma power51_r3_8_eq : ∀ k : Fin 16, power51Expr 3 8 k = power51_r3_8 k := by decide +kernel
lemma power51_r3_9_eq : ∀ k : Fin 16, power51Expr 3 9 k = power51_r3_9 k := by decide +kernel
lemma power51_r3_10_eq : ∀ k : Fin 16, power51Expr 3 10 k = power51_r3_10 k := by decide +kernel
lemma power51_r3_11_eq : ∀ k : Fin 16, power51Expr 3 11 k = power51_r3_11 k := by decide +kernel
lemma power51_r3_12_eq : ∀ k : Fin 16, power51Expr 3 12 k = power51_r3_12 k := by decide +kernel
lemma power51_r3_13_eq : ∀ k : Fin 16, power51Expr 3 13 k = power51_r3_13 k := by decide +kernel
lemma power51_r3_14_eq : ∀ k : Fin 16, power51Expr 3 14 k = power51_r3_14 k := by decide +kernel
lemma power51_r3_15_eq : ∀ k : Fin 16, power51Expr 3 15 k = power51_r3_15 k := by decide +kernel
lemma power51_r3_eq (i k : Fin 16) : power51Expr 3 i k = power51_r3 i k := by
  fin_cases i
  · exact power51_r3_0_eq k
  · exact power51_r3_1_eq k
  · exact power51_r3_2_eq k
  · exact power51_r3_3_eq k
  · exact power51_r3_4_eq k
  · exact power51_r3_5_eq k
  · exact power51_r3_6_eq k
  · exact power51_r3_7_eq k
  · exact power51_r3_8_eq k
  · exact power51_r3_9_eq k
  · exact power51_r3_10_eq k
  · exact power51_r3_11_eq k
  · exact power51_r3_12_eq k
  · exact power51_r3_13_eq k
  · exact power51_r3_14_eq k
  · exact power51_r3_15_eq k
lemma power51_r4_0_eq : ∀ k : Fin 16, power51Expr 4 0 k = power51_r4_0 k := by decide +kernel
lemma power51_r4_1_eq : ∀ k : Fin 16, power51Expr 4 1 k = power51_r4_1 k := by decide +kernel
lemma power51_r4_2_eq : ∀ k : Fin 16, power51Expr 4 2 k = power51_r4_2 k := by decide +kernel
lemma power51_r4_3_eq : ∀ k : Fin 16, power51Expr 4 3 k = power51_r4_3 k := by decide +kernel
lemma power51_r4_4_eq : ∀ k : Fin 16, power51Expr 4 4 k = power51_r4_4 k := by decide +kernel
lemma power51_r4_5_eq : ∀ k : Fin 16, power51Expr 4 5 k = power51_r4_5 k := by decide +kernel
lemma power51_r4_6_eq : ∀ k : Fin 16, power51Expr 4 6 k = power51_r4_6 k := by decide +kernel
lemma power51_r4_7_eq : ∀ k : Fin 16, power51Expr 4 7 k = power51_r4_7 k := by decide +kernel
lemma power51_r4_8_eq : ∀ k : Fin 16, power51Expr 4 8 k = power51_r4_8 k := by decide +kernel
lemma power51_r4_9_eq : ∀ k : Fin 16, power51Expr 4 9 k = power51_r4_9 k := by decide +kernel
lemma power51_r4_10_eq : ∀ k : Fin 16, power51Expr 4 10 k = power51_r4_10 k := by decide +kernel
lemma power51_r4_11_eq : ∀ k : Fin 16, power51Expr 4 11 k = power51_r4_11 k := by decide +kernel
lemma power51_r4_12_eq : ∀ k : Fin 16, power51Expr 4 12 k = power51_r4_12 k := by decide +kernel
lemma power51_r4_13_eq : ∀ k : Fin 16, power51Expr 4 13 k = power51_r4_13 k := by decide +kernel
lemma power51_r4_14_eq : ∀ k : Fin 16, power51Expr 4 14 k = power51_r4_14 k := by decide +kernel
lemma power51_r4_15_eq : ∀ k : Fin 16, power51Expr 4 15 k = power51_r4_15 k := by decide +kernel
lemma power51_r4_eq (i k : Fin 16) : power51Expr 4 i k = power51_r4 i k := by
  fin_cases i
  · exact power51_r4_0_eq k
  · exact power51_r4_1_eq k
  · exact power51_r4_2_eq k
  · exact power51_r4_3_eq k
  · exact power51_r4_4_eq k
  · exact power51_r4_5_eq k
  · exact power51_r4_6_eq k
  · exact power51_r4_7_eq k
  · exact power51_r4_8_eq k
  · exact power51_r4_9_eq k
  · exact power51_r4_10_eq k
  · exact power51_r4_11_eq k
  · exact power51_r4_12_eq k
  · exact power51_r4_13_eq k
  · exact power51_r4_14_eq k
  · exact power51_r4_15_eq k
lemma power51_r5_0_eq : ∀ k : Fin 16, power51Expr 5 0 k = power51_r5_0 k := by decide +kernel
lemma power51_r5_1_eq : ∀ k : Fin 16, power51Expr 5 1 k = power51_r5_1 k := by decide +kernel
lemma power51_r5_2_eq : ∀ k : Fin 16, power51Expr 5 2 k = power51_r5_2 k := by decide +kernel
lemma power51_r5_3_eq : ∀ k : Fin 16, power51Expr 5 3 k = power51_r5_3 k := by decide +kernel
lemma power51_r5_4_eq : ∀ k : Fin 16, power51Expr 5 4 k = power51_r5_4 k := by decide +kernel
lemma power51_r5_5_eq : ∀ k : Fin 16, power51Expr 5 5 k = power51_r5_5 k := by decide +kernel
lemma power51_r5_6_eq : ∀ k : Fin 16, power51Expr 5 6 k = power51_r5_6 k := by decide +kernel
lemma power51_r5_7_eq : ∀ k : Fin 16, power51Expr 5 7 k = power51_r5_7 k := by decide +kernel
lemma power51_r5_8_eq : ∀ k : Fin 16, power51Expr 5 8 k = power51_r5_8 k := by decide +kernel
lemma power51_r5_9_eq : ∀ k : Fin 16, power51Expr 5 9 k = power51_r5_9 k := by decide +kernel
lemma power51_r5_10_eq : ∀ k : Fin 16, power51Expr 5 10 k = power51_r5_10 k := by decide +kernel
lemma power51_r5_11_eq : ∀ k : Fin 16, power51Expr 5 11 k = power51_r5_11 k := by decide +kernel
lemma power51_r5_12_eq : ∀ k : Fin 16, power51Expr 5 12 k = power51_r5_12 k := by decide +kernel
lemma power51_r5_13_eq : ∀ k : Fin 16, power51Expr 5 13 k = power51_r5_13 k := by decide +kernel
lemma power51_r5_14_eq : ∀ k : Fin 16, power51Expr 5 14 k = power51_r5_14 k := by decide +kernel
lemma power51_r5_15_eq : ∀ k : Fin 16, power51Expr 5 15 k = power51_r5_15 k := by decide +kernel
lemma power51_r5_eq (i k : Fin 16) : power51Expr 5 i k = power51_r5 i k := by
  fin_cases i
  · exact power51_r5_0_eq k
  · exact power51_r5_1_eq k
  · exact power51_r5_2_eq k
  · exact power51_r5_3_eq k
  · exact power51_r5_4_eq k
  · exact power51_r5_5_eq k
  · exact power51_r5_6_eq k
  · exact power51_r5_7_eq k
  · exact power51_r5_8_eq k
  · exact power51_r5_9_eq k
  · exact power51_r5_10_eq k
  · exact power51_r5_11_eq k
  · exact power51_r5_12_eq k
  · exact power51_r5_13_eq k
  · exact power51_r5_14_eq k
  · exact power51_r5_15_eq k
lemma power51_eq (j : Fin 6) (i k : Fin 16) : power51Expr j i k = power51 j i k := by
  fin_cases j
  · exact power51_r0_eq i k
  · exact power51_r1_eq i k
  · exact power51_r2_eq i k
  · exact power51_r3_eq i k
  · exact power51_r4_eq i k
  · exact power51_r5_eq i k
lemma power51_contains (j : Fin 6) (i k : Fin 16) :
    (power51 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(51:ℕ))) := by
  rw [← power51_eq]
  unfold power51Expr
  convert exp_direct_step_g (power50_contains_g j i k) (gridRows_contains_g j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns60
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
lemma column51_0_r0_0_eq : ∀ k : Fin 16, column51_0Expr 0 0 k = column51_0_r0_0 k := by decide +kernel
lemma column51_0_r0_1_eq : ∀ k : Fin 16, column51_0Expr 0 1 k = column51_0_r0_1 k := by decide +kernel
lemma column51_0_r0_2_eq : ∀ k : Fin 16, column51_0Expr 0 2 k = column51_0_r0_2 k := by decide +kernel
lemma column51_0_r0_3_eq : ∀ k : Fin 16, column51_0Expr 0 3 k = column51_0_r0_3 k := by decide +kernel
lemma column51_0_r0_4_eq : ∀ k : Fin 16, column51_0Expr 0 4 k = column51_0_r0_4 k := by decide +kernel
lemma column51_0_r0_5_eq : ∀ k : Fin 16, column51_0Expr 0 5 k = column51_0_r0_5 k := by decide +kernel
lemma column51_0_r0_6_eq : ∀ k : Fin 16, column51_0Expr 0 6 k = column51_0_r0_6 k := by decide +kernel
lemma column51_0_r0_7_eq : ∀ k : Fin 16, column51_0Expr 0 7 k = column51_0_r0_7 k := by decide +kernel
lemma column51_0_r0_8_eq : ∀ k : Fin 16, column51_0Expr 0 8 k = column51_0_r0_8 k := by decide +kernel
lemma column51_0_r0_9_eq : ∀ k : Fin 16, column51_0Expr 0 9 k = column51_0_r0_9 k := by decide +kernel
lemma column51_0_r0_10_eq : ∀ k : Fin 16, column51_0Expr 0 10 k = column51_0_r0_10 k := by decide +kernel
lemma column51_0_r0_11_eq : ∀ k : Fin 16, column51_0Expr 0 11 k = column51_0_r0_11 k := by decide +kernel
lemma column51_0_r0_12_eq : ∀ k : Fin 16, column51_0Expr 0 12 k = column51_0_r0_12 k := by decide +kernel
lemma column51_0_r0_13_eq : ∀ k : Fin 16, column51_0Expr 0 13 k = column51_0_r0_13 k := by decide +kernel
lemma column51_0_r0_14_eq : ∀ k : Fin 16, column51_0Expr 0 14 k = column51_0_r0_14 k := by decide +kernel
lemma column51_0_r0_15_eq : ∀ k : Fin 16, column51_0Expr 0 15 k = column51_0_r0_15 k := by decide +kernel
lemma column51_0_r0_eq (i k : Fin 16) : column51_0Expr 0 i k = column51_0_r0 i k := by
  fin_cases i
  · exact column51_0_r0_0_eq k
  · exact column51_0_r0_1_eq k
  · exact column51_0_r0_2_eq k
  · exact column51_0_r0_3_eq k
  · exact column51_0_r0_4_eq k
  · exact column51_0_r0_5_eq k
  · exact column51_0_r0_6_eq k
  · exact column51_0_r0_7_eq k
  · exact column51_0_r0_8_eq k
  · exact column51_0_r0_9_eq k
  · exact column51_0_r0_10_eq k
  · exact column51_0_r0_11_eq k
  · exact column51_0_r0_12_eq k
  · exact column51_0_r0_13_eq k
  · exact column51_0_r0_14_eq k
  · exact column51_0_r0_15_eq k
lemma column51_0_r1_0_eq : ∀ k : Fin 16, column51_0Expr 1 0 k = column51_0_r1_0 k := by decide +kernel
lemma column51_0_r1_1_eq : ∀ k : Fin 16, column51_0Expr 1 1 k = column51_0_r1_1 k := by decide +kernel
lemma column51_0_r1_2_eq : ∀ k : Fin 16, column51_0Expr 1 2 k = column51_0_r1_2 k := by decide +kernel
lemma column51_0_r1_3_eq : ∀ k : Fin 16, column51_0Expr 1 3 k = column51_0_r1_3 k := by decide +kernel
lemma column51_0_r1_4_eq : ∀ k : Fin 16, column51_0Expr 1 4 k = column51_0_r1_4 k := by decide +kernel
lemma column51_0_r1_5_eq : ∀ k : Fin 16, column51_0Expr 1 5 k = column51_0_r1_5 k := by decide +kernel
lemma column51_0_r1_6_eq : ∀ k : Fin 16, column51_0Expr 1 6 k = column51_0_r1_6 k := by decide +kernel
lemma column51_0_r1_7_eq : ∀ k : Fin 16, column51_0Expr 1 7 k = column51_0_r1_7 k := by decide +kernel
lemma column51_0_r1_8_eq : ∀ k : Fin 16, column51_0Expr 1 8 k = column51_0_r1_8 k := by decide +kernel
lemma column51_0_r1_9_eq : ∀ k : Fin 16, column51_0Expr 1 9 k = column51_0_r1_9 k := by decide +kernel
lemma column51_0_r1_10_eq : ∀ k : Fin 16, column51_0Expr 1 10 k = column51_0_r1_10 k := by decide +kernel
lemma column51_0_r1_11_eq : ∀ k : Fin 16, column51_0Expr 1 11 k = column51_0_r1_11 k := by decide +kernel
lemma column51_0_r1_12_eq : ∀ k : Fin 16, column51_0Expr 1 12 k = column51_0_r1_12 k := by decide +kernel
lemma column51_0_r1_13_eq : ∀ k : Fin 16, column51_0Expr 1 13 k = column51_0_r1_13 k := by decide +kernel
lemma column51_0_r1_14_eq : ∀ k : Fin 16, column51_0Expr 1 14 k = column51_0_r1_14 k := by decide +kernel
lemma column51_0_r1_15_eq : ∀ k : Fin 16, column51_0Expr 1 15 k = column51_0_r1_15 k := by decide +kernel
lemma column51_0_r1_eq (i k : Fin 16) : column51_0Expr 1 i k = column51_0_r1 i k := by
  fin_cases i
  · exact column51_0_r1_0_eq k
  · exact column51_0_r1_1_eq k
  · exact column51_0_r1_2_eq k
  · exact column51_0_r1_3_eq k
  · exact column51_0_r1_4_eq k
  · exact column51_0_r1_5_eq k
  · exact column51_0_r1_6_eq k
  · exact column51_0_r1_7_eq k
  · exact column51_0_r1_8_eq k
  · exact column51_0_r1_9_eq k
  · exact column51_0_r1_10_eq k
  · exact column51_0_r1_11_eq k
  · exact column51_0_r1_12_eq k
  · exact column51_0_r1_13_eq k
  · exact column51_0_r1_14_eq k
  · exact column51_0_r1_15_eq k
lemma column51_0_r2_0_eq : ∀ k : Fin 16, column51_0Expr 2 0 k = column51_0_r2_0 k := by decide +kernel
lemma column51_0_r2_1_eq : ∀ k : Fin 16, column51_0Expr 2 1 k = column51_0_r2_1 k := by decide +kernel
lemma column51_0_r2_2_eq : ∀ k : Fin 16, column51_0Expr 2 2 k = column51_0_r2_2 k := by decide +kernel
lemma column51_0_r2_3_eq : ∀ k : Fin 16, column51_0Expr 2 3 k = column51_0_r2_3 k := by decide +kernel
lemma column51_0_r2_4_eq : ∀ k : Fin 16, column51_0Expr 2 4 k = column51_0_r2_4 k := by decide +kernel
lemma column51_0_r2_5_eq : ∀ k : Fin 16, column51_0Expr 2 5 k = column51_0_r2_5 k := by decide +kernel
lemma column51_0_r2_6_eq : ∀ k : Fin 16, column51_0Expr 2 6 k = column51_0_r2_6 k := by decide +kernel
lemma column51_0_r2_7_eq : ∀ k : Fin 16, column51_0Expr 2 7 k = column51_0_r2_7 k := by decide +kernel
lemma column51_0_r2_8_eq : ∀ k : Fin 16, column51_0Expr 2 8 k = column51_0_r2_8 k := by decide +kernel
lemma column51_0_r2_9_eq : ∀ k : Fin 16, column51_0Expr 2 9 k = column51_0_r2_9 k := by decide +kernel
lemma column51_0_r2_10_eq : ∀ k : Fin 16, column51_0Expr 2 10 k = column51_0_r2_10 k := by decide +kernel
lemma column51_0_r2_11_eq : ∀ k : Fin 16, column51_0Expr 2 11 k = column51_0_r2_11 k := by decide +kernel
lemma column51_0_r2_12_eq : ∀ k : Fin 16, column51_0Expr 2 12 k = column51_0_r2_12 k := by decide +kernel
lemma column51_0_r2_13_eq : ∀ k : Fin 16, column51_0Expr 2 13 k = column51_0_r2_13 k := by decide +kernel
lemma column51_0_r2_14_eq : ∀ k : Fin 16, column51_0Expr 2 14 k = column51_0_r2_14 k := by decide +kernel
lemma column51_0_r2_15_eq : ∀ k : Fin 16, column51_0Expr 2 15 k = column51_0_r2_15 k := by decide +kernel
lemma column51_0_r2_eq (i k : Fin 16) : column51_0Expr 2 i k = column51_0_r2 i k := by
  fin_cases i
  · exact column51_0_r2_0_eq k
  · exact column51_0_r2_1_eq k
  · exact column51_0_r2_2_eq k
  · exact column51_0_r2_3_eq k
  · exact column51_0_r2_4_eq k
  · exact column51_0_r2_5_eq k
  · exact column51_0_r2_6_eq k
  · exact column51_0_r2_7_eq k
  · exact column51_0_r2_8_eq k
  · exact column51_0_r2_9_eq k
  · exact column51_0_r2_10_eq k
  · exact column51_0_r2_11_eq k
  · exact column51_0_r2_12_eq k
  · exact column51_0_r2_13_eq k
  · exact column51_0_r2_14_eq k
  · exact column51_0_r2_15_eq k
lemma column51_0_r3_0_eq : ∀ k : Fin 16, column51_0Expr 3 0 k = column51_0_r3_0 k := by decide +kernel
lemma column51_0_r3_1_eq : ∀ k : Fin 16, column51_0Expr 3 1 k = column51_0_r3_1 k := by decide +kernel
lemma column51_0_r3_2_eq : ∀ k : Fin 16, column51_0Expr 3 2 k = column51_0_r3_2 k := by decide +kernel
lemma column51_0_r3_3_eq : ∀ k : Fin 16, column51_0Expr 3 3 k = column51_0_r3_3 k := by decide +kernel
lemma column51_0_r3_4_eq : ∀ k : Fin 16, column51_0Expr 3 4 k = column51_0_r3_4 k := by decide +kernel
lemma column51_0_r3_5_eq : ∀ k : Fin 16, column51_0Expr 3 5 k = column51_0_r3_5 k := by decide +kernel
lemma column51_0_r3_6_eq : ∀ k : Fin 16, column51_0Expr 3 6 k = column51_0_r3_6 k := by decide +kernel
lemma column51_0_r3_7_eq : ∀ k : Fin 16, column51_0Expr 3 7 k = column51_0_r3_7 k := by decide +kernel
lemma column51_0_r3_8_eq : ∀ k : Fin 16, column51_0Expr 3 8 k = column51_0_r3_8 k := by decide +kernel
lemma column51_0_r3_9_eq : ∀ k : Fin 16, column51_0Expr 3 9 k = column51_0_r3_9 k := by decide +kernel
lemma column51_0_r3_10_eq : ∀ k : Fin 16, column51_0Expr 3 10 k = column51_0_r3_10 k := by decide +kernel
lemma column51_0_r3_11_eq : ∀ k : Fin 16, column51_0Expr 3 11 k = column51_0_r3_11 k := by decide +kernel
lemma column51_0_r3_12_eq : ∀ k : Fin 16, column51_0Expr 3 12 k = column51_0_r3_12 k := by decide +kernel
lemma column51_0_r3_13_eq : ∀ k : Fin 16, column51_0Expr 3 13 k = column51_0_r3_13 k := by decide +kernel
lemma column51_0_r3_14_eq : ∀ k : Fin 16, column51_0Expr 3 14 k = column51_0_r3_14 k := by decide +kernel
lemma column51_0_r3_15_eq : ∀ k : Fin 16, column51_0Expr 3 15 k = column51_0_r3_15 k := by decide +kernel
lemma column51_0_r3_eq (i k : Fin 16) : column51_0Expr 3 i k = column51_0_r3 i k := by
  fin_cases i
  · exact column51_0_r3_0_eq k
  · exact column51_0_r3_1_eq k
  · exact column51_0_r3_2_eq k
  · exact column51_0_r3_3_eq k
  · exact column51_0_r3_4_eq k
  · exact column51_0_r3_5_eq k
  · exact column51_0_r3_6_eq k
  · exact column51_0_r3_7_eq k
  · exact column51_0_r3_8_eq k
  · exact column51_0_r3_9_eq k
  · exact column51_0_r3_10_eq k
  · exact column51_0_r3_11_eq k
  · exact column51_0_r3_12_eq k
  · exact column51_0_r3_13_eq k
  · exact column51_0_r3_14_eq k
  · exact column51_0_r3_15_eq k
lemma column51_0_r4_0_eq : ∀ k : Fin 16, column51_0Expr 4 0 k = column51_0_r4_0 k := by decide +kernel
lemma column51_0_r4_1_eq : ∀ k : Fin 16, column51_0Expr 4 1 k = column51_0_r4_1 k := by decide +kernel
lemma column51_0_r4_2_eq : ∀ k : Fin 16, column51_0Expr 4 2 k = column51_0_r4_2 k := by decide +kernel
lemma column51_0_r4_3_eq : ∀ k : Fin 16, column51_0Expr 4 3 k = column51_0_r4_3 k := by decide +kernel
lemma column51_0_r4_4_eq : ∀ k : Fin 16, column51_0Expr 4 4 k = column51_0_r4_4 k := by decide +kernel
lemma column51_0_r4_5_eq : ∀ k : Fin 16, column51_0Expr 4 5 k = column51_0_r4_5 k := by decide +kernel
lemma column51_0_r4_6_eq : ∀ k : Fin 16, column51_0Expr 4 6 k = column51_0_r4_6 k := by decide +kernel
lemma column51_0_r4_7_eq : ∀ k : Fin 16, column51_0Expr 4 7 k = column51_0_r4_7 k := by decide +kernel
lemma column51_0_r4_8_eq : ∀ k : Fin 16, column51_0Expr 4 8 k = column51_0_r4_8 k := by decide +kernel
lemma column51_0_r4_9_eq : ∀ k : Fin 16, column51_0Expr 4 9 k = column51_0_r4_9 k := by decide +kernel
lemma column51_0_r4_10_eq : ∀ k : Fin 16, column51_0Expr 4 10 k = column51_0_r4_10 k := by decide +kernel
lemma column51_0_r4_11_eq : ∀ k : Fin 16, column51_0Expr 4 11 k = column51_0_r4_11 k := by decide +kernel
lemma column51_0_r4_12_eq : ∀ k : Fin 16, column51_0Expr 4 12 k = column51_0_r4_12 k := by decide +kernel
lemma column51_0_r4_13_eq : ∀ k : Fin 16, column51_0Expr 4 13 k = column51_0_r4_13 k := by decide +kernel
lemma column51_0_r4_14_eq : ∀ k : Fin 16, column51_0Expr 4 14 k = column51_0_r4_14 k := by decide +kernel
lemma column51_0_r4_15_eq : ∀ k : Fin 16, column51_0Expr 4 15 k = column51_0_r4_15 k := by decide +kernel
lemma column51_0_r4_eq (i k : Fin 16) : column51_0Expr 4 i k = column51_0_r4 i k := by
  fin_cases i
  · exact column51_0_r4_0_eq k
  · exact column51_0_r4_1_eq k
  · exact column51_0_r4_2_eq k
  · exact column51_0_r4_3_eq k
  · exact column51_0_r4_4_eq k
  · exact column51_0_r4_5_eq k
  · exact column51_0_r4_6_eq k
  · exact column51_0_r4_7_eq k
  · exact column51_0_r4_8_eq k
  · exact column51_0_r4_9_eq k
  · exact column51_0_r4_10_eq k
  · exact column51_0_r4_11_eq k
  · exact column51_0_r4_12_eq k
  · exact column51_0_r4_13_eq k
  · exact column51_0_r4_14_eq k
  · exact column51_0_r4_15_eq k
lemma column51_0_r5_0_eq : ∀ k : Fin 16, column51_0Expr 5 0 k = column51_0_r5_0 k := by decide +kernel
lemma column51_0_r5_1_eq : ∀ k : Fin 16, column51_0Expr 5 1 k = column51_0_r5_1 k := by decide +kernel
lemma column51_0_r5_2_eq : ∀ k : Fin 16, column51_0Expr 5 2 k = column51_0_r5_2 k := by decide +kernel
lemma column51_0_r5_3_eq : ∀ k : Fin 16, column51_0Expr 5 3 k = column51_0_r5_3 k := by decide +kernel
lemma column51_0_r5_4_eq : ∀ k : Fin 16, column51_0Expr 5 4 k = column51_0_r5_4 k := by decide +kernel
lemma column51_0_r5_5_eq : ∀ k : Fin 16, column51_0Expr 5 5 k = column51_0_r5_5 k := by decide +kernel
lemma column51_0_r5_6_eq : ∀ k : Fin 16, column51_0Expr 5 6 k = column51_0_r5_6 k := by decide +kernel
lemma column51_0_r5_7_eq : ∀ k : Fin 16, column51_0Expr 5 7 k = column51_0_r5_7 k := by decide +kernel
lemma column51_0_r5_8_eq : ∀ k : Fin 16, column51_0Expr 5 8 k = column51_0_r5_8 k := by decide +kernel
lemma column51_0_r5_9_eq : ∀ k : Fin 16, column51_0Expr 5 9 k = column51_0_r5_9 k := by decide +kernel
lemma column51_0_r5_10_eq : ∀ k : Fin 16, column51_0Expr 5 10 k = column51_0_r5_10 k := by decide +kernel
lemma column51_0_r5_11_eq : ∀ k : Fin 16, column51_0Expr 5 11 k = column51_0_r5_11 k := by decide +kernel
lemma column51_0_r5_12_eq : ∀ k : Fin 16, column51_0Expr 5 12 k = column51_0_r5_12 k := by decide +kernel
lemma column51_0_r5_13_eq : ∀ k : Fin 16, column51_0Expr 5 13 k = column51_0_r5_13 k := by decide +kernel
lemma column51_0_r5_14_eq : ∀ k : Fin 16, column51_0Expr 5 14 k = column51_0_r5_14 k := by decide +kernel
lemma column51_0_r5_15_eq : ∀ k : Fin 16, column51_0Expr 5 15 k = column51_0_r5_15 k := by decide +kernel
lemma column51_0_r5_eq (i k : Fin 16) : column51_0Expr 5 i k = column51_0_r5 i k := by
  fin_cases i
  · exact column51_0_r5_0_eq k
  · exact column51_0_r5_1_eq k
  · exact column51_0_r5_2_eq k
  · exact column51_0_r5_3_eq k
  · exact column51_0_r5_4_eq k
  · exact column51_0_r5_5_eq k
  · exact column51_0_r5_6_eq k
  · exact column51_0_r5_7_eq k
  · exact column51_0_r5_8_eq k
  · exact column51_0_r5_9_eq k
  · exact column51_0_r5_10_eq k
  · exact column51_0_r5_11_eq k
  · exact column51_0_r5_12_eq k
  · exact column51_0_r5_13_eq k
  · exact column51_0_r5_14_eq k
  · exact column51_0_r5_15_eq k
lemma column51_0_eq (j : Fin 6) (i k : Fin 16) : column51_0Expr j i k = column51_0 j i k := by
  fin_cases j
  · exact column51_0_r0_eq i k
  · exact column51_0_r1_eq i k
  · exact column51_0_r2_eq i k
  · exact column51_0_r3_eq i k
  · exact column51_0_r4_eq i k
  · exact column51_0_r5_eq i k
lemma column51_0_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (column51_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 51 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column51_0_eq,basisFunction_wave_g,← mul_assoc]
  unfold column51_0Expr
  apply CBox.contains_mul_g
  · rw [← waveAmplitude_mod false 51 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp3_0_contains j i k
  · exact power51_contains j i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.column51_0_contains_g_oai := @OAI.SharpPlanar.CachedData.column51_0_contains_g_oai
