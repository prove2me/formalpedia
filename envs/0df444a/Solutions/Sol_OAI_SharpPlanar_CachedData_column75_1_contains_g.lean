-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.column75_1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:54:31.011262+00:00
-- url     : https://prove2.me/submissions/d5aa6fd6-a3f4-441c-8375-06ecc4fc0009

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G206
import Definitions.Def_OAIQ098G283
import Definitions.Def_OAIQ098G342
import Theorems.Thm_OAI_SharpPlanar_CachedData_power74_contains_g
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
lemma amp3_10_0_eq : ∀ k : Fin 16, amp3_1Expr 0 0 k = amp3_10_0 k := by decide +kernel
lemma amp3_10_1_eq : ∀ k : Fin 16, amp3_1Expr 0 1 k = amp3_10_1 k := by decide +kernel
lemma amp3_10_2_eq : ∀ k : Fin 16, amp3_1Expr 0 2 k = amp3_10_2 k := by decide +kernel
lemma amp3_10_3_eq : ∀ k : Fin 16, amp3_1Expr 0 3 k = amp3_10_3 k := by decide +kernel
lemma amp3_10_4_eq : ∀ k : Fin 16, amp3_1Expr 0 4 k = amp3_10_4 k := by decide +kernel
lemma amp3_10_5_eq : ∀ k : Fin 16, amp3_1Expr 0 5 k = amp3_10_5 k := by decide +kernel
lemma amp3_10_6_eq : ∀ k : Fin 16, amp3_1Expr 0 6 k = amp3_10_6 k := by decide +kernel
lemma amp3_10_7_eq : ∀ k : Fin 16, amp3_1Expr 0 7 k = amp3_10_7 k := by decide +kernel
lemma amp3_10_8_eq : ∀ k : Fin 16, amp3_1Expr 0 8 k = amp3_10_8 k := by decide +kernel
lemma amp3_10_9_eq : ∀ k : Fin 16, amp3_1Expr 0 9 k = amp3_10_9 k := by decide +kernel
lemma amp3_10_10_eq : ∀ k : Fin 16, amp3_1Expr 0 10 k = amp3_10_10 k := by decide +kernel
lemma amp3_10_11_eq : ∀ k : Fin 16, amp3_1Expr 0 11 k = amp3_10_11 k := by decide +kernel
lemma amp3_10_12_eq : ∀ k : Fin 16, amp3_1Expr 0 12 k = amp3_10_12 k := by decide +kernel
lemma amp3_10_13_eq : ∀ k : Fin 16, amp3_1Expr 0 13 k = amp3_10_13 k := by decide +kernel
lemma amp3_10_14_eq : ∀ k : Fin 16, amp3_1Expr 0 14 k = amp3_10_14 k := by decide +kernel
lemma amp3_10_15_eq : ∀ k : Fin 16, amp3_1Expr 0 15 k = amp3_10_15 k := by decide +kernel
lemma amp3_10_eq (i k : Fin 16) : amp3_1Expr 0 i k = amp3_10 i k := by
  fin_cases i
  · exact amp3_10_0_eq k
  · exact amp3_10_1_eq k
  · exact amp3_10_2_eq k
  · exact amp3_10_3_eq k
  · exact amp3_10_4_eq k
  · exact amp3_10_5_eq k
  · exact amp3_10_6_eq k
  · exact amp3_10_7_eq k
  · exact amp3_10_8_eq k
  · exact amp3_10_9_eq k
  · exact amp3_10_10_eq k
  · exact amp3_10_11_eq k
  · exact amp3_10_12_eq k
  · exact amp3_10_13_eq k
  · exact amp3_10_14_eq k
  · exact amp3_10_15_eq k
lemma amp3_11_0_eq : ∀ k : Fin 16, amp3_1Expr 1 0 k = amp3_11_0 k := by decide +kernel
lemma amp3_11_1_eq : ∀ k : Fin 16, amp3_1Expr 1 1 k = amp3_11_1 k := by decide +kernel
lemma amp3_11_2_eq : ∀ k : Fin 16, amp3_1Expr 1 2 k = amp3_11_2 k := by decide +kernel
lemma amp3_11_3_eq : ∀ k : Fin 16, amp3_1Expr 1 3 k = amp3_11_3 k := by decide +kernel
lemma amp3_11_4_eq : ∀ k : Fin 16, amp3_1Expr 1 4 k = amp3_11_4 k := by decide +kernel
lemma amp3_11_5_eq : ∀ k : Fin 16, amp3_1Expr 1 5 k = amp3_11_5 k := by decide +kernel
lemma amp3_11_6_eq : ∀ k : Fin 16, amp3_1Expr 1 6 k = amp3_11_6 k := by decide +kernel
lemma amp3_11_7_eq : ∀ k : Fin 16, amp3_1Expr 1 7 k = amp3_11_7 k := by decide +kernel
lemma amp3_11_8_eq : ∀ k : Fin 16, amp3_1Expr 1 8 k = amp3_11_8 k := by decide +kernel
lemma amp3_11_9_eq : ∀ k : Fin 16, amp3_1Expr 1 9 k = amp3_11_9 k := by decide +kernel
lemma amp3_11_10_eq : ∀ k : Fin 16, amp3_1Expr 1 10 k = amp3_11_10 k := by decide +kernel
lemma amp3_11_11_eq : ∀ k : Fin 16, amp3_1Expr 1 11 k = amp3_11_11 k := by decide +kernel
lemma amp3_11_12_eq : ∀ k : Fin 16, amp3_1Expr 1 12 k = amp3_11_12 k := by decide +kernel
lemma amp3_11_13_eq : ∀ k : Fin 16, amp3_1Expr 1 13 k = amp3_11_13 k := by decide +kernel
lemma amp3_11_14_eq : ∀ k : Fin 16, amp3_1Expr 1 14 k = amp3_11_14 k := by decide +kernel
lemma amp3_11_15_eq : ∀ k : Fin 16, amp3_1Expr 1 15 k = amp3_11_15 k := by decide +kernel
lemma amp3_11_eq (i k : Fin 16) : amp3_1Expr 1 i k = amp3_11 i k := by
  fin_cases i
  · exact amp3_11_0_eq k
  · exact amp3_11_1_eq k
  · exact amp3_11_2_eq k
  · exact amp3_11_3_eq k
  · exact amp3_11_4_eq k
  · exact amp3_11_5_eq k
  · exact amp3_11_6_eq k
  · exact amp3_11_7_eq k
  · exact amp3_11_8_eq k
  · exact amp3_11_9_eq k
  · exact amp3_11_10_eq k
  · exact amp3_11_11_eq k
  · exact amp3_11_12_eq k
  · exact amp3_11_13_eq k
  · exact amp3_11_14_eq k
  · exact amp3_11_15_eq k
lemma amp3_12_0_eq : ∀ k : Fin 16, amp3_1Expr 2 0 k = amp3_12_0 k := by decide +kernel
lemma amp3_12_1_eq : ∀ k : Fin 16, amp3_1Expr 2 1 k = amp3_12_1 k := by decide +kernel
lemma amp3_12_2_eq : ∀ k : Fin 16, amp3_1Expr 2 2 k = amp3_12_2 k := by decide +kernel
lemma amp3_12_3_eq : ∀ k : Fin 16, amp3_1Expr 2 3 k = amp3_12_3 k := by decide +kernel
lemma amp3_12_4_eq : ∀ k : Fin 16, amp3_1Expr 2 4 k = amp3_12_4 k := by decide +kernel
lemma amp3_12_5_eq : ∀ k : Fin 16, amp3_1Expr 2 5 k = amp3_12_5 k := by decide +kernel
lemma amp3_12_6_eq : ∀ k : Fin 16, amp3_1Expr 2 6 k = amp3_12_6 k := by decide +kernel
lemma amp3_12_7_eq : ∀ k : Fin 16, amp3_1Expr 2 7 k = amp3_12_7 k := by decide +kernel
lemma amp3_12_8_eq : ∀ k : Fin 16, amp3_1Expr 2 8 k = amp3_12_8 k := by decide +kernel
lemma amp3_12_9_eq : ∀ k : Fin 16, amp3_1Expr 2 9 k = amp3_12_9 k := by decide +kernel
lemma amp3_12_10_eq : ∀ k : Fin 16, amp3_1Expr 2 10 k = amp3_12_10 k := by decide +kernel
lemma amp3_12_11_eq : ∀ k : Fin 16, amp3_1Expr 2 11 k = amp3_12_11 k := by decide +kernel
lemma amp3_12_12_eq : ∀ k : Fin 16, amp3_1Expr 2 12 k = amp3_12_12 k := by decide +kernel
lemma amp3_12_13_eq : ∀ k : Fin 16, amp3_1Expr 2 13 k = amp3_12_13 k := by decide +kernel
lemma amp3_12_14_eq : ∀ k : Fin 16, amp3_1Expr 2 14 k = amp3_12_14 k := by decide +kernel
lemma amp3_12_15_eq : ∀ k : Fin 16, amp3_1Expr 2 15 k = amp3_12_15 k := by decide +kernel
lemma amp3_12_eq (i k : Fin 16) : amp3_1Expr 2 i k = amp3_12 i k := by
  fin_cases i
  · exact amp3_12_0_eq k
  · exact amp3_12_1_eq k
  · exact amp3_12_2_eq k
  · exact amp3_12_3_eq k
  · exact amp3_12_4_eq k
  · exact amp3_12_5_eq k
  · exact amp3_12_6_eq k
  · exact amp3_12_7_eq k
  · exact amp3_12_8_eq k
  · exact amp3_12_9_eq k
  · exact amp3_12_10_eq k
  · exact amp3_12_11_eq k
  · exact amp3_12_12_eq k
  · exact amp3_12_13_eq k
  · exact amp3_12_14_eq k
  · exact amp3_12_15_eq k
lemma amp3_13_0_eq : ∀ k : Fin 16, amp3_1Expr 3 0 k = amp3_13_0 k := by decide +kernel
lemma amp3_13_1_eq : ∀ k : Fin 16, amp3_1Expr 3 1 k = amp3_13_1 k := by decide +kernel
lemma amp3_13_2_eq : ∀ k : Fin 16, amp3_1Expr 3 2 k = amp3_13_2 k := by decide +kernel
lemma amp3_13_3_eq : ∀ k : Fin 16, amp3_1Expr 3 3 k = amp3_13_3 k := by decide +kernel
lemma amp3_13_4_eq : ∀ k : Fin 16, amp3_1Expr 3 4 k = amp3_13_4 k := by decide +kernel
lemma amp3_13_5_eq : ∀ k : Fin 16, amp3_1Expr 3 5 k = amp3_13_5 k := by decide +kernel
lemma amp3_13_6_eq : ∀ k : Fin 16, amp3_1Expr 3 6 k = amp3_13_6 k := by decide +kernel
lemma amp3_13_7_eq : ∀ k : Fin 16, amp3_1Expr 3 7 k = amp3_13_7 k := by decide +kernel
lemma amp3_13_8_eq : ∀ k : Fin 16, amp3_1Expr 3 8 k = amp3_13_8 k := by decide +kernel
lemma amp3_13_9_eq : ∀ k : Fin 16, amp3_1Expr 3 9 k = amp3_13_9 k := by decide +kernel
lemma amp3_13_10_eq : ∀ k : Fin 16, amp3_1Expr 3 10 k = amp3_13_10 k := by decide +kernel
lemma amp3_13_11_eq : ∀ k : Fin 16, amp3_1Expr 3 11 k = amp3_13_11 k := by decide +kernel
lemma amp3_13_12_eq : ∀ k : Fin 16, amp3_1Expr 3 12 k = amp3_13_12 k := by decide +kernel
lemma amp3_13_13_eq : ∀ k : Fin 16, amp3_1Expr 3 13 k = amp3_13_13 k := by decide +kernel
lemma amp3_13_14_eq : ∀ k : Fin 16, amp3_1Expr 3 14 k = amp3_13_14 k := by decide +kernel
lemma amp3_13_15_eq : ∀ k : Fin 16, amp3_1Expr 3 15 k = amp3_13_15 k := by decide +kernel
lemma amp3_13_eq (i k : Fin 16) : amp3_1Expr 3 i k = amp3_13 i k := by
  fin_cases i
  · exact amp3_13_0_eq k
  · exact amp3_13_1_eq k
  · exact amp3_13_2_eq k
  · exact amp3_13_3_eq k
  · exact amp3_13_4_eq k
  · exact amp3_13_5_eq k
  · exact amp3_13_6_eq k
  · exact amp3_13_7_eq k
  · exact amp3_13_8_eq k
  · exact amp3_13_9_eq k
  · exact amp3_13_10_eq k
  · exact amp3_13_11_eq k
  · exact amp3_13_12_eq k
  · exact amp3_13_13_eq k
  · exact amp3_13_14_eq k
  · exact amp3_13_15_eq k
lemma amp3_14_0_eq : ∀ k : Fin 16, amp3_1Expr 4 0 k = amp3_14_0 k := by decide +kernel
lemma amp3_14_1_eq : ∀ k : Fin 16, amp3_1Expr 4 1 k = amp3_14_1 k := by decide +kernel
lemma amp3_14_2_eq : ∀ k : Fin 16, amp3_1Expr 4 2 k = amp3_14_2 k := by decide +kernel
lemma amp3_14_3_eq : ∀ k : Fin 16, amp3_1Expr 4 3 k = amp3_14_3 k := by decide +kernel
lemma amp3_14_4_eq : ∀ k : Fin 16, amp3_1Expr 4 4 k = amp3_14_4 k := by decide +kernel
lemma amp3_14_5_eq : ∀ k : Fin 16, amp3_1Expr 4 5 k = amp3_14_5 k := by decide +kernel
lemma amp3_14_6_eq : ∀ k : Fin 16, amp3_1Expr 4 6 k = amp3_14_6 k := by decide +kernel
lemma amp3_14_7_eq : ∀ k : Fin 16, amp3_1Expr 4 7 k = amp3_14_7 k := by decide +kernel
lemma amp3_14_8_eq : ∀ k : Fin 16, amp3_1Expr 4 8 k = amp3_14_8 k := by decide +kernel
lemma amp3_14_9_eq : ∀ k : Fin 16, amp3_1Expr 4 9 k = amp3_14_9 k := by decide +kernel
lemma amp3_14_10_eq : ∀ k : Fin 16, amp3_1Expr 4 10 k = amp3_14_10 k := by decide +kernel
lemma amp3_14_11_eq : ∀ k : Fin 16, amp3_1Expr 4 11 k = amp3_14_11 k := by decide +kernel
lemma amp3_14_12_eq : ∀ k : Fin 16, amp3_1Expr 4 12 k = amp3_14_12 k := by decide +kernel
lemma amp3_14_13_eq : ∀ k : Fin 16, amp3_1Expr 4 13 k = amp3_14_13 k := by decide +kernel
lemma amp3_14_14_eq : ∀ k : Fin 16, amp3_1Expr 4 14 k = amp3_14_14 k := by decide +kernel
lemma amp3_14_15_eq : ∀ k : Fin 16, amp3_1Expr 4 15 k = amp3_14_15 k := by decide +kernel
lemma amp3_14_eq (i k : Fin 16) : amp3_1Expr 4 i k = amp3_14 i k := by
  fin_cases i
  · exact amp3_14_0_eq k
  · exact amp3_14_1_eq k
  · exact amp3_14_2_eq k
  · exact amp3_14_3_eq k
  · exact amp3_14_4_eq k
  · exact amp3_14_5_eq k
  · exact amp3_14_6_eq k
  · exact amp3_14_7_eq k
  · exact amp3_14_8_eq k
  · exact amp3_14_9_eq k
  · exact amp3_14_10_eq k
  · exact amp3_14_11_eq k
  · exact amp3_14_12_eq k
  · exact amp3_14_13_eq k
  · exact amp3_14_14_eq k
  · exact amp3_14_15_eq k
lemma amp3_15_0_eq : ∀ k : Fin 16, amp3_1Expr 5 0 k = amp3_15_0 k := by decide +kernel
lemma amp3_15_1_eq : ∀ k : Fin 16, amp3_1Expr 5 1 k = amp3_15_1 k := by decide +kernel
lemma amp3_15_2_eq : ∀ k : Fin 16, amp3_1Expr 5 2 k = amp3_15_2 k := by decide +kernel
lemma amp3_15_3_eq : ∀ k : Fin 16, amp3_1Expr 5 3 k = amp3_15_3 k := by decide +kernel
lemma amp3_15_4_eq : ∀ k : Fin 16, amp3_1Expr 5 4 k = amp3_15_4 k := by decide +kernel
lemma amp3_15_5_eq : ∀ k : Fin 16, amp3_1Expr 5 5 k = amp3_15_5 k := by decide +kernel
lemma amp3_15_6_eq : ∀ k : Fin 16, amp3_1Expr 5 6 k = amp3_15_6 k := by decide +kernel
lemma amp3_15_7_eq : ∀ k : Fin 16, amp3_1Expr 5 7 k = amp3_15_7 k := by decide +kernel
lemma amp3_15_8_eq : ∀ k : Fin 16, amp3_1Expr 5 8 k = amp3_15_8 k := by decide +kernel
lemma amp3_15_9_eq : ∀ k : Fin 16, amp3_1Expr 5 9 k = amp3_15_9 k := by decide +kernel
lemma amp3_15_10_eq : ∀ k : Fin 16, amp3_1Expr 5 10 k = amp3_15_10 k := by decide +kernel
lemma amp3_15_11_eq : ∀ k : Fin 16, amp3_1Expr 5 11 k = amp3_15_11 k := by decide +kernel
lemma amp3_15_12_eq : ∀ k : Fin 16, amp3_1Expr 5 12 k = amp3_15_12 k := by decide +kernel
lemma amp3_15_13_eq : ∀ k : Fin 16, amp3_1Expr 5 13 k = amp3_15_13 k := by decide +kernel
lemma amp3_15_14_eq : ∀ k : Fin 16, amp3_1Expr 5 14 k = amp3_15_14 k := by decide +kernel
lemma amp3_15_15_eq : ∀ k : Fin 16, amp3_1Expr 5 15 k = amp3_15_15 k := by decide +kernel
lemma amp3_15_eq (i k : Fin 16) : amp3_1Expr 5 i k = amp3_15 i k := by
  fin_cases i
  · exact amp3_15_0_eq k
  · exact amp3_15_1_eq k
  · exact amp3_15_2_eq k
  · exact amp3_15_3_eq k
  · exact amp3_15_4_eq k
  · exact amp3_15_5_eq k
  · exact amp3_15_6_eq k
  · exact amp3_15_7_eq k
  · exact amp3_15_8_eq k
  · exact amp3_15_9_eq k
  · exact amp3_15_10_eq k
  · exact amp3_15_11_eq k
  · exact amp3_15_12_eq k
  · exact amp3_15_13_eq k
  · exact amp3_15_14_eq k
  · exact amp3_15_15_eq k
lemma amp3_1_eq (j : Fin 6) (i k : Fin 16) : amp3_1Expr j i k = amp3_1 j i k := by
  fin_cases j
  · exact amp3_10_eq i k
  · exact amp3_11_eq i k
  · exact amp3_12_eq i k
  · exact amp3_13_eq i k
  · exact amp3_14_eq i k
  · exact amp3_15_eq i k
lemma amp3_1_contains (j : Fin 6) (i k : Fin 16) :
    (amp3_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude true 3 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← amp3_1_eq]
  exact CBox.contains_mul_g (rcast_contains_g (weightRows_contains_g i k))
    (waveAmplitudeBox_contains_g (gridRows_contains_g j i k) (aLookup_contains_g 3 j) (bLookup_contains_g 3 j) true)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers80
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
lemma power75_r0_0_eq : ∀ k : Fin 16, power75Expr 0 0 k = power75_r0_0 k := by decide +kernel
lemma power75_r0_1_eq : ∀ k : Fin 16, power75Expr 0 1 k = power75_r0_1 k := by decide +kernel
lemma power75_r0_2_eq : ∀ k : Fin 16, power75Expr 0 2 k = power75_r0_2 k := by decide +kernel
lemma power75_r0_3_eq : ∀ k : Fin 16, power75Expr 0 3 k = power75_r0_3 k := by decide +kernel
lemma power75_r0_4_eq : ∀ k : Fin 16, power75Expr 0 4 k = power75_r0_4 k := by decide +kernel
lemma power75_r0_5_eq : ∀ k : Fin 16, power75Expr 0 5 k = power75_r0_5 k := by decide +kernel
lemma power75_r0_6_eq : ∀ k : Fin 16, power75Expr 0 6 k = power75_r0_6 k := by decide +kernel
lemma power75_r0_7_eq : ∀ k : Fin 16, power75Expr 0 7 k = power75_r0_7 k := by decide +kernel
lemma power75_r0_8_eq : ∀ k : Fin 16, power75Expr 0 8 k = power75_r0_8 k := by decide +kernel
lemma power75_r0_9_eq : ∀ k : Fin 16, power75Expr 0 9 k = power75_r0_9 k := by decide +kernel
lemma power75_r0_10_eq : ∀ k : Fin 16, power75Expr 0 10 k = power75_r0_10 k := by decide +kernel
lemma power75_r0_11_eq : ∀ k : Fin 16, power75Expr 0 11 k = power75_r0_11 k := by decide +kernel
lemma power75_r0_12_eq : ∀ k : Fin 16, power75Expr 0 12 k = power75_r0_12 k := by decide +kernel
lemma power75_r0_13_eq : ∀ k : Fin 16, power75Expr 0 13 k = power75_r0_13 k := by decide +kernel
lemma power75_r0_14_eq : ∀ k : Fin 16, power75Expr 0 14 k = power75_r0_14 k := by decide +kernel
lemma power75_r0_15_eq : ∀ k : Fin 16, power75Expr 0 15 k = power75_r0_15 k := by decide +kernel
lemma power75_r0_eq (i k : Fin 16) : power75Expr 0 i k = power75_r0 i k := by
  fin_cases i
  · exact power75_r0_0_eq k
  · exact power75_r0_1_eq k
  · exact power75_r0_2_eq k
  · exact power75_r0_3_eq k
  · exact power75_r0_4_eq k
  · exact power75_r0_5_eq k
  · exact power75_r0_6_eq k
  · exact power75_r0_7_eq k
  · exact power75_r0_8_eq k
  · exact power75_r0_9_eq k
  · exact power75_r0_10_eq k
  · exact power75_r0_11_eq k
  · exact power75_r0_12_eq k
  · exact power75_r0_13_eq k
  · exact power75_r0_14_eq k
  · exact power75_r0_15_eq k
lemma power75_r1_0_eq : ∀ k : Fin 16, power75Expr 1 0 k = power75_r1_0 k := by decide +kernel
lemma power75_r1_1_eq : ∀ k : Fin 16, power75Expr 1 1 k = power75_r1_1 k := by decide +kernel
lemma power75_r1_2_eq : ∀ k : Fin 16, power75Expr 1 2 k = power75_r1_2 k := by decide +kernel
lemma power75_r1_3_eq : ∀ k : Fin 16, power75Expr 1 3 k = power75_r1_3 k := by decide +kernel
lemma power75_r1_4_eq : ∀ k : Fin 16, power75Expr 1 4 k = power75_r1_4 k := by decide +kernel
lemma power75_r1_5_eq : ∀ k : Fin 16, power75Expr 1 5 k = power75_r1_5 k := by decide +kernel
lemma power75_r1_6_eq : ∀ k : Fin 16, power75Expr 1 6 k = power75_r1_6 k := by decide +kernel
lemma power75_r1_7_eq : ∀ k : Fin 16, power75Expr 1 7 k = power75_r1_7 k := by decide +kernel
lemma power75_r1_8_eq : ∀ k : Fin 16, power75Expr 1 8 k = power75_r1_8 k := by decide +kernel
lemma power75_r1_9_eq : ∀ k : Fin 16, power75Expr 1 9 k = power75_r1_9 k := by decide +kernel
lemma power75_r1_10_eq : ∀ k : Fin 16, power75Expr 1 10 k = power75_r1_10 k := by decide +kernel
lemma power75_r1_11_eq : ∀ k : Fin 16, power75Expr 1 11 k = power75_r1_11 k := by decide +kernel
lemma power75_r1_12_eq : ∀ k : Fin 16, power75Expr 1 12 k = power75_r1_12 k := by decide +kernel
lemma power75_r1_13_eq : ∀ k : Fin 16, power75Expr 1 13 k = power75_r1_13 k := by decide +kernel
lemma power75_r1_14_eq : ∀ k : Fin 16, power75Expr 1 14 k = power75_r1_14 k := by decide +kernel
lemma power75_r1_15_eq : ∀ k : Fin 16, power75Expr 1 15 k = power75_r1_15 k := by decide +kernel
lemma power75_r1_eq (i k : Fin 16) : power75Expr 1 i k = power75_r1 i k := by
  fin_cases i
  · exact power75_r1_0_eq k
  · exact power75_r1_1_eq k
  · exact power75_r1_2_eq k
  · exact power75_r1_3_eq k
  · exact power75_r1_4_eq k
  · exact power75_r1_5_eq k
  · exact power75_r1_6_eq k
  · exact power75_r1_7_eq k
  · exact power75_r1_8_eq k
  · exact power75_r1_9_eq k
  · exact power75_r1_10_eq k
  · exact power75_r1_11_eq k
  · exact power75_r1_12_eq k
  · exact power75_r1_13_eq k
  · exact power75_r1_14_eq k
  · exact power75_r1_15_eq k
lemma power75_r2_0_eq : ∀ k : Fin 16, power75Expr 2 0 k = power75_r2_0 k := by decide +kernel
lemma power75_r2_1_eq : ∀ k : Fin 16, power75Expr 2 1 k = power75_r2_1 k := by decide +kernel
lemma power75_r2_2_eq : ∀ k : Fin 16, power75Expr 2 2 k = power75_r2_2 k := by decide +kernel
lemma power75_r2_3_eq : ∀ k : Fin 16, power75Expr 2 3 k = power75_r2_3 k := by decide +kernel
lemma power75_r2_4_eq : ∀ k : Fin 16, power75Expr 2 4 k = power75_r2_4 k := by decide +kernel
lemma power75_r2_5_eq : ∀ k : Fin 16, power75Expr 2 5 k = power75_r2_5 k := by decide +kernel
lemma power75_r2_6_eq : ∀ k : Fin 16, power75Expr 2 6 k = power75_r2_6 k := by decide +kernel
lemma power75_r2_7_eq : ∀ k : Fin 16, power75Expr 2 7 k = power75_r2_7 k := by decide +kernel
lemma power75_r2_8_eq : ∀ k : Fin 16, power75Expr 2 8 k = power75_r2_8 k := by decide +kernel
lemma power75_r2_9_eq : ∀ k : Fin 16, power75Expr 2 9 k = power75_r2_9 k := by decide +kernel
lemma power75_r2_10_eq : ∀ k : Fin 16, power75Expr 2 10 k = power75_r2_10 k := by decide +kernel
lemma power75_r2_11_eq : ∀ k : Fin 16, power75Expr 2 11 k = power75_r2_11 k := by decide +kernel
lemma power75_r2_12_eq : ∀ k : Fin 16, power75Expr 2 12 k = power75_r2_12 k := by decide +kernel
lemma power75_r2_13_eq : ∀ k : Fin 16, power75Expr 2 13 k = power75_r2_13 k := by decide +kernel
lemma power75_r2_14_eq : ∀ k : Fin 16, power75Expr 2 14 k = power75_r2_14 k := by decide +kernel
lemma power75_r2_15_eq : ∀ k : Fin 16, power75Expr 2 15 k = power75_r2_15 k := by decide +kernel
lemma power75_r2_eq (i k : Fin 16) : power75Expr 2 i k = power75_r2 i k := by
  fin_cases i
  · exact power75_r2_0_eq k
  · exact power75_r2_1_eq k
  · exact power75_r2_2_eq k
  · exact power75_r2_3_eq k
  · exact power75_r2_4_eq k
  · exact power75_r2_5_eq k
  · exact power75_r2_6_eq k
  · exact power75_r2_7_eq k
  · exact power75_r2_8_eq k
  · exact power75_r2_9_eq k
  · exact power75_r2_10_eq k
  · exact power75_r2_11_eq k
  · exact power75_r2_12_eq k
  · exact power75_r2_13_eq k
  · exact power75_r2_14_eq k
  · exact power75_r2_15_eq k
lemma power75_r3_0_eq : ∀ k : Fin 16, power75Expr 3 0 k = power75_r3_0 k := by decide +kernel
lemma power75_r3_1_eq : ∀ k : Fin 16, power75Expr 3 1 k = power75_r3_1 k := by decide +kernel
lemma power75_r3_2_eq : ∀ k : Fin 16, power75Expr 3 2 k = power75_r3_2 k := by decide +kernel
lemma power75_r3_3_eq : ∀ k : Fin 16, power75Expr 3 3 k = power75_r3_3 k := by decide +kernel
lemma power75_r3_4_eq : ∀ k : Fin 16, power75Expr 3 4 k = power75_r3_4 k := by decide +kernel
lemma power75_r3_5_eq : ∀ k : Fin 16, power75Expr 3 5 k = power75_r3_5 k := by decide +kernel
lemma power75_r3_6_eq : ∀ k : Fin 16, power75Expr 3 6 k = power75_r3_6 k := by decide +kernel
lemma power75_r3_7_eq : ∀ k : Fin 16, power75Expr 3 7 k = power75_r3_7 k := by decide +kernel
lemma power75_r3_8_eq : ∀ k : Fin 16, power75Expr 3 8 k = power75_r3_8 k := by decide +kernel
lemma power75_r3_9_eq : ∀ k : Fin 16, power75Expr 3 9 k = power75_r3_9 k := by decide +kernel
lemma power75_r3_10_eq : ∀ k : Fin 16, power75Expr 3 10 k = power75_r3_10 k := by decide +kernel
lemma power75_r3_11_eq : ∀ k : Fin 16, power75Expr 3 11 k = power75_r3_11 k := by decide +kernel
lemma power75_r3_12_eq : ∀ k : Fin 16, power75Expr 3 12 k = power75_r3_12 k := by decide +kernel
lemma power75_r3_13_eq : ∀ k : Fin 16, power75Expr 3 13 k = power75_r3_13 k := by decide +kernel
lemma power75_r3_14_eq : ∀ k : Fin 16, power75Expr 3 14 k = power75_r3_14 k := by decide +kernel
lemma power75_r3_15_eq : ∀ k : Fin 16, power75Expr 3 15 k = power75_r3_15 k := by decide +kernel
lemma power75_r3_eq (i k : Fin 16) : power75Expr 3 i k = power75_r3 i k := by
  fin_cases i
  · exact power75_r3_0_eq k
  · exact power75_r3_1_eq k
  · exact power75_r3_2_eq k
  · exact power75_r3_3_eq k
  · exact power75_r3_4_eq k
  · exact power75_r3_5_eq k
  · exact power75_r3_6_eq k
  · exact power75_r3_7_eq k
  · exact power75_r3_8_eq k
  · exact power75_r3_9_eq k
  · exact power75_r3_10_eq k
  · exact power75_r3_11_eq k
  · exact power75_r3_12_eq k
  · exact power75_r3_13_eq k
  · exact power75_r3_14_eq k
  · exact power75_r3_15_eq k
lemma power75_r4_0_eq : ∀ k : Fin 16, power75Expr 4 0 k = power75_r4_0 k := by decide +kernel
lemma power75_r4_1_eq : ∀ k : Fin 16, power75Expr 4 1 k = power75_r4_1 k := by decide +kernel
lemma power75_r4_2_eq : ∀ k : Fin 16, power75Expr 4 2 k = power75_r4_2 k := by decide +kernel
lemma power75_r4_3_eq : ∀ k : Fin 16, power75Expr 4 3 k = power75_r4_3 k := by decide +kernel
lemma power75_r4_4_eq : ∀ k : Fin 16, power75Expr 4 4 k = power75_r4_4 k := by decide +kernel
lemma power75_r4_5_eq : ∀ k : Fin 16, power75Expr 4 5 k = power75_r4_5 k := by decide +kernel
lemma power75_r4_6_eq : ∀ k : Fin 16, power75Expr 4 6 k = power75_r4_6 k := by decide +kernel
lemma power75_r4_7_eq : ∀ k : Fin 16, power75Expr 4 7 k = power75_r4_7 k := by decide +kernel
lemma power75_r4_8_eq : ∀ k : Fin 16, power75Expr 4 8 k = power75_r4_8 k := by decide +kernel
lemma power75_r4_9_eq : ∀ k : Fin 16, power75Expr 4 9 k = power75_r4_9 k := by decide +kernel
lemma power75_r4_10_eq : ∀ k : Fin 16, power75Expr 4 10 k = power75_r4_10 k := by decide +kernel
lemma power75_r4_11_eq : ∀ k : Fin 16, power75Expr 4 11 k = power75_r4_11 k := by decide +kernel
lemma power75_r4_12_eq : ∀ k : Fin 16, power75Expr 4 12 k = power75_r4_12 k := by decide +kernel
lemma power75_r4_13_eq : ∀ k : Fin 16, power75Expr 4 13 k = power75_r4_13 k := by decide +kernel
lemma power75_r4_14_eq : ∀ k : Fin 16, power75Expr 4 14 k = power75_r4_14 k := by decide +kernel
lemma power75_r4_15_eq : ∀ k : Fin 16, power75Expr 4 15 k = power75_r4_15 k := by decide +kernel
lemma power75_r4_eq (i k : Fin 16) : power75Expr 4 i k = power75_r4 i k := by
  fin_cases i
  · exact power75_r4_0_eq k
  · exact power75_r4_1_eq k
  · exact power75_r4_2_eq k
  · exact power75_r4_3_eq k
  · exact power75_r4_4_eq k
  · exact power75_r4_5_eq k
  · exact power75_r4_6_eq k
  · exact power75_r4_7_eq k
  · exact power75_r4_8_eq k
  · exact power75_r4_9_eq k
  · exact power75_r4_10_eq k
  · exact power75_r4_11_eq k
  · exact power75_r4_12_eq k
  · exact power75_r4_13_eq k
  · exact power75_r4_14_eq k
  · exact power75_r4_15_eq k
lemma power75_r5_0_eq : ∀ k : Fin 16, power75Expr 5 0 k = power75_r5_0 k := by decide +kernel
lemma power75_r5_1_eq : ∀ k : Fin 16, power75Expr 5 1 k = power75_r5_1 k := by decide +kernel
lemma power75_r5_2_eq : ∀ k : Fin 16, power75Expr 5 2 k = power75_r5_2 k := by decide +kernel
lemma power75_r5_3_eq : ∀ k : Fin 16, power75Expr 5 3 k = power75_r5_3 k := by decide +kernel
lemma power75_r5_4_eq : ∀ k : Fin 16, power75Expr 5 4 k = power75_r5_4 k := by decide +kernel
lemma power75_r5_5_eq : ∀ k : Fin 16, power75Expr 5 5 k = power75_r5_5 k := by decide +kernel
lemma power75_r5_6_eq : ∀ k : Fin 16, power75Expr 5 6 k = power75_r5_6 k := by decide +kernel
lemma power75_r5_7_eq : ∀ k : Fin 16, power75Expr 5 7 k = power75_r5_7 k := by decide +kernel
lemma power75_r5_8_eq : ∀ k : Fin 16, power75Expr 5 8 k = power75_r5_8 k := by decide +kernel
lemma power75_r5_9_eq : ∀ k : Fin 16, power75Expr 5 9 k = power75_r5_9 k := by decide +kernel
lemma power75_r5_10_eq : ∀ k : Fin 16, power75Expr 5 10 k = power75_r5_10 k := by decide +kernel
lemma power75_r5_11_eq : ∀ k : Fin 16, power75Expr 5 11 k = power75_r5_11 k := by decide +kernel
lemma power75_r5_12_eq : ∀ k : Fin 16, power75Expr 5 12 k = power75_r5_12 k := by decide +kernel
lemma power75_r5_13_eq : ∀ k : Fin 16, power75Expr 5 13 k = power75_r5_13 k := by decide +kernel
lemma power75_r5_14_eq : ∀ k : Fin 16, power75Expr 5 14 k = power75_r5_14 k := by decide +kernel
lemma power75_r5_15_eq : ∀ k : Fin 16, power75Expr 5 15 k = power75_r5_15 k := by decide +kernel
lemma power75_r5_eq (i k : Fin 16) : power75Expr 5 i k = power75_r5 i k := by
  fin_cases i
  · exact power75_r5_0_eq k
  · exact power75_r5_1_eq k
  · exact power75_r5_2_eq k
  · exact power75_r5_3_eq k
  · exact power75_r5_4_eq k
  · exact power75_r5_5_eq k
  · exact power75_r5_6_eq k
  · exact power75_r5_7_eq k
  · exact power75_r5_8_eq k
  · exact power75_r5_9_eq k
  · exact power75_r5_10_eq k
  · exact power75_r5_11_eq k
  · exact power75_r5_12_eq k
  · exact power75_r5_13_eq k
  · exact power75_r5_14_eq k
  · exact power75_r5_15_eq k
lemma power75_eq (j : Fin 6) (i k : Fin 16) : power75Expr j i k = power75 j i k := by
  fin_cases j
  · exact power75_r0_eq i k
  · exact power75_r1_eq i k
  · exact power75_r2_eq i k
  · exact power75_r3_eq i k
  · exact power75_r4_eq i k
  · exact power75_r5_eq i k
lemma power75_contains (j : Fin 6) (i k : Fin 16) :
    (power75 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(75:ℕ))) := by
  rw [← power75_eq]
  unfold power75Expr
  convert exp_direct_step_g (power74_contains_g j i k) (gridRows_contains_g j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns80
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
lemma column75_1_r0_0_eq : ∀ k : Fin 16, column75_1Expr 0 0 k = column75_1_r0_0 k := by decide +kernel
lemma column75_1_r0_1_eq : ∀ k : Fin 16, column75_1Expr 0 1 k = column75_1_r0_1 k := by decide +kernel
lemma column75_1_r0_2_eq : ∀ k : Fin 16, column75_1Expr 0 2 k = column75_1_r0_2 k := by decide +kernel
lemma column75_1_r0_3_eq : ∀ k : Fin 16, column75_1Expr 0 3 k = column75_1_r0_3 k := by decide +kernel
lemma column75_1_r0_4_eq : ∀ k : Fin 16, column75_1Expr 0 4 k = column75_1_r0_4 k := by decide +kernel
lemma column75_1_r0_5_eq : ∀ k : Fin 16, column75_1Expr 0 5 k = column75_1_r0_5 k := by decide +kernel
lemma column75_1_r0_6_eq : ∀ k : Fin 16, column75_1Expr 0 6 k = column75_1_r0_6 k := by decide +kernel
lemma column75_1_r0_7_eq : ∀ k : Fin 16, column75_1Expr 0 7 k = column75_1_r0_7 k := by decide +kernel
lemma column75_1_r0_8_eq : ∀ k : Fin 16, column75_1Expr 0 8 k = column75_1_r0_8 k := by decide +kernel
lemma column75_1_r0_9_eq : ∀ k : Fin 16, column75_1Expr 0 9 k = column75_1_r0_9 k := by decide +kernel
lemma column75_1_r0_10_eq : ∀ k : Fin 16, column75_1Expr 0 10 k = column75_1_r0_10 k := by decide +kernel
lemma column75_1_r0_11_eq : ∀ k : Fin 16, column75_1Expr 0 11 k = column75_1_r0_11 k := by decide +kernel
lemma column75_1_r0_12_eq : ∀ k : Fin 16, column75_1Expr 0 12 k = column75_1_r0_12 k := by decide +kernel
lemma column75_1_r0_13_eq : ∀ k : Fin 16, column75_1Expr 0 13 k = column75_1_r0_13 k := by decide +kernel
lemma column75_1_r0_14_eq : ∀ k : Fin 16, column75_1Expr 0 14 k = column75_1_r0_14 k := by decide +kernel
lemma column75_1_r0_15_eq : ∀ k : Fin 16, column75_1Expr 0 15 k = column75_1_r0_15 k := by decide +kernel
lemma column75_1_r0_eq (i k : Fin 16) : column75_1Expr 0 i k = column75_1_r0 i k := by
  fin_cases i
  · exact column75_1_r0_0_eq k
  · exact column75_1_r0_1_eq k
  · exact column75_1_r0_2_eq k
  · exact column75_1_r0_3_eq k
  · exact column75_1_r0_4_eq k
  · exact column75_1_r0_5_eq k
  · exact column75_1_r0_6_eq k
  · exact column75_1_r0_7_eq k
  · exact column75_1_r0_8_eq k
  · exact column75_1_r0_9_eq k
  · exact column75_1_r0_10_eq k
  · exact column75_1_r0_11_eq k
  · exact column75_1_r0_12_eq k
  · exact column75_1_r0_13_eq k
  · exact column75_1_r0_14_eq k
  · exact column75_1_r0_15_eq k
lemma column75_1_r1_0_eq : ∀ k : Fin 16, column75_1Expr 1 0 k = column75_1_r1_0 k := by decide +kernel
lemma column75_1_r1_1_eq : ∀ k : Fin 16, column75_1Expr 1 1 k = column75_1_r1_1 k := by decide +kernel
lemma column75_1_r1_2_eq : ∀ k : Fin 16, column75_1Expr 1 2 k = column75_1_r1_2 k := by decide +kernel
lemma column75_1_r1_3_eq : ∀ k : Fin 16, column75_1Expr 1 3 k = column75_1_r1_3 k := by decide +kernel
lemma column75_1_r1_4_eq : ∀ k : Fin 16, column75_1Expr 1 4 k = column75_1_r1_4 k := by decide +kernel
lemma column75_1_r1_5_eq : ∀ k : Fin 16, column75_1Expr 1 5 k = column75_1_r1_5 k := by decide +kernel
lemma column75_1_r1_6_eq : ∀ k : Fin 16, column75_1Expr 1 6 k = column75_1_r1_6 k := by decide +kernel
lemma column75_1_r1_7_eq : ∀ k : Fin 16, column75_1Expr 1 7 k = column75_1_r1_7 k := by decide +kernel
lemma column75_1_r1_8_eq : ∀ k : Fin 16, column75_1Expr 1 8 k = column75_1_r1_8 k := by decide +kernel
lemma column75_1_r1_9_eq : ∀ k : Fin 16, column75_1Expr 1 9 k = column75_1_r1_9 k := by decide +kernel
lemma column75_1_r1_10_eq : ∀ k : Fin 16, column75_1Expr 1 10 k = column75_1_r1_10 k := by decide +kernel
lemma column75_1_r1_11_eq : ∀ k : Fin 16, column75_1Expr 1 11 k = column75_1_r1_11 k := by decide +kernel
lemma column75_1_r1_12_eq : ∀ k : Fin 16, column75_1Expr 1 12 k = column75_1_r1_12 k := by decide +kernel
lemma column75_1_r1_13_eq : ∀ k : Fin 16, column75_1Expr 1 13 k = column75_1_r1_13 k := by decide +kernel
lemma column75_1_r1_14_eq : ∀ k : Fin 16, column75_1Expr 1 14 k = column75_1_r1_14 k := by decide +kernel
lemma column75_1_r1_15_eq : ∀ k : Fin 16, column75_1Expr 1 15 k = column75_1_r1_15 k := by decide +kernel
lemma column75_1_r1_eq (i k : Fin 16) : column75_1Expr 1 i k = column75_1_r1 i k := by
  fin_cases i
  · exact column75_1_r1_0_eq k
  · exact column75_1_r1_1_eq k
  · exact column75_1_r1_2_eq k
  · exact column75_1_r1_3_eq k
  · exact column75_1_r1_4_eq k
  · exact column75_1_r1_5_eq k
  · exact column75_1_r1_6_eq k
  · exact column75_1_r1_7_eq k
  · exact column75_1_r1_8_eq k
  · exact column75_1_r1_9_eq k
  · exact column75_1_r1_10_eq k
  · exact column75_1_r1_11_eq k
  · exact column75_1_r1_12_eq k
  · exact column75_1_r1_13_eq k
  · exact column75_1_r1_14_eq k
  · exact column75_1_r1_15_eq k
lemma column75_1_r2_0_eq : ∀ k : Fin 16, column75_1Expr 2 0 k = column75_1_r2_0 k := by decide +kernel
lemma column75_1_r2_1_eq : ∀ k : Fin 16, column75_1Expr 2 1 k = column75_1_r2_1 k := by decide +kernel
lemma column75_1_r2_2_eq : ∀ k : Fin 16, column75_1Expr 2 2 k = column75_1_r2_2 k := by decide +kernel
lemma column75_1_r2_3_eq : ∀ k : Fin 16, column75_1Expr 2 3 k = column75_1_r2_3 k := by decide +kernel
lemma column75_1_r2_4_eq : ∀ k : Fin 16, column75_1Expr 2 4 k = column75_1_r2_4 k := by decide +kernel
lemma column75_1_r2_5_eq : ∀ k : Fin 16, column75_1Expr 2 5 k = column75_1_r2_5 k := by decide +kernel
lemma column75_1_r2_6_eq : ∀ k : Fin 16, column75_1Expr 2 6 k = column75_1_r2_6 k := by decide +kernel
lemma column75_1_r2_7_eq : ∀ k : Fin 16, column75_1Expr 2 7 k = column75_1_r2_7 k := by decide +kernel
lemma column75_1_r2_8_eq : ∀ k : Fin 16, column75_1Expr 2 8 k = column75_1_r2_8 k := by decide +kernel
lemma column75_1_r2_9_eq : ∀ k : Fin 16, column75_1Expr 2 9 k = column75_1_r2_9 k := by decide +kernel
lemma column75_1_r2_10_eq : ∀ k : Fin 16, column75_1Expr 2 10 k = column75_1_r2_10 k := by decide +kernel
lemma column75_1_r2_11_eq : ∀ k : Fin 16, column75_1Expr 2 11 k = column75_1_r2_11 k := by decide +kernel
lemma column75_1_r2_12_eq : ∀ k : Fin 16, column75_1Expr 2 12 k = column75_1_r2_12 k := by decide +kernel
lemma column75_1_r2_13_eq : ∀ k : Fin 16, column75_1Expr 2 13 k = column75_1_r2_13 k := by decide +kernel
lemma column75_1_r2_14_eq : ∀ k : Fin 16, column75_1Expr 2 14 k = column75_1_r2_14 k := by decide +kernel
lemma column75_1_r2_15_eq : ∀ k : Fin 16, column75_1Expr 2 15 k = column75_1_r2_15 k := by decide +kernel
lemma column75_1_r2_eq (i k : Fin 16) : column75_1Expr 2 i k = column75_1_r2 i k := by
  fin_cases i
  · exact column75_1_r2_0_eq k
  · exact column75_1_r2_1_eq k
  · exact column75_1_r2_2_eq k
  · exact column75_1_r2_3_eq k
  · exact column75_1_r2_4_eq k
  · exact column75_1_r2_5_eq k
  · exact column75_1_r2_6_eq k
  · exact column75_1_r2_7_eq k
  · exact column75_1_r2_8_eq k
  · exact column75_1_r2_9_eq k
  · exact column75_1_r2_10_eq k
  · exact column75_1_r2_11_eq k
  · exact column75_1_r2_12_eq k
  · exact column75_1_r2_13_eq k
  · exact column75_1_r2_14_eq k
  · exact column75_1_r2_15_eq k
lemma column75_1_r3_0_eq : ∀ k : Fin 16, column75_1Expr 3 0 k = column75_1_r3_0 k := by decide +kernel
lemma column75_1_r3_1_eq : ∀ k : Fin 16, column75_1Expr 3 1 k = column75_1_r3_1 k := by decide +kernel
lemma column75_1_r3_2_eq : ∀ k : Fin 16, column75_1Expr 3 2 k = column75_1_r3_2 k := by decide +kernel
lemma column75_1_r3_3_eq : ∀ k : Fin 16, column75_1Expr 3 3 k = column75_1_r3_3 k := by decide +kernel
lemma column75_1_r3_4_eq : ∀ k : Fin 16, column75_1Expr 3 4 k = column75_1_r3_4 k := by decide +kernel
lemma column75_1_r3_5_eq : ∀ k : Fin 16, column75_1Expr 3 5 k = column75_1_r3_5 k := by decide +kernel
lemma column75_1_r3_6_eq : ∀ k : Fin 16, column75_1Expr 3 6 k = column75_1_r3_6 k := by decide +kernel
lemma column75_1_r3_7_eq : ∀ k : Fin 16, column75_1Expr 3 7 k = column75_1_r3_7 k := by decide +kernel
lemma column75_1_r3_8_eq : ∀ k : Fin 16, column75_1Expr 3 8 k = column75_1_r3_8 k := by decide +kernel
lemma column75_1_r3_9_eq : ∀ k : Fin 16, column75_1Expr 3 9 k = column75_1_r3_9 k := by decide +kernel
lemma column75_1_r3_10_eq : ∀ k : Fin 16, column75_1Expr 3 10 k = column75_1_r3_10 k := by decide +kernel
lemma column75_1_r3_11_eq : ∀ k : Fin 16, column75_1Expr 3 11 k = column75_1_r3_11 k := by decide +kernel
lemma column75_1_r3_12_eq : ∀ k : Fin 16, column75_1Expr 3 12 k = column75_1_r3_12 k := by decide +kernel
lemma column75_1_r3_13_eq : ∀ k : Fin 16, column75_1Expr 3 13 k = column75_1_r3_13 k := by decide +kernel
lemma column75_1_r3_14_eq : ∀ k : Fin 16, column75_1Expr 3 14 k = column75_1_r3_14 k := by decide +kernel
lemma column75_1_r3_15_eq : ∀ k : Fin 16, column75_1Expr 3 15 k = column75_1_r3_15 k := by decide +kernel
lemma column75_1_r3_eq (i k : Fin 16) : column75_1Expr 3 i k = column75_1_r3 i k := by
  fin_cases i
  · exact column75_1_r3_0_eq k
  · exact column75_1_r3_1_eq k
  · exact column75_1_r3_2_eq k
  · exact column75_1_r3_3_eq k
  · exact column75_1_r3_4_eq k
  · exact column75_1_r3_5_eq k
  · exact column75_1_r3_6_eq k
  · exact column75_1_r3_7_eq k
  · exact column75_1_r3_8_eq k
  · exact column75_1_r3_9_eq k
  · exact column75_1_r3_10_eq k
  · exact column75_1_r3_11_eq k
  · exact column75_1_r3_12_eq k
  · exact column75_1_r3_13_eq k
  · exact column75_1_r3_14_eq k
  · exact column75_1_r3_15_eq k
lemma column75_1_r4_0_eq : ∀ k : Fin 16, column75_1Expr 4 0 k = column75_1_r4_0 k := by decide +kernel
lemma column75_1_r4_1_eq : ∀ k : Fin 16, column75_1Expr 4 1 k = column75_1_r4_1 k := by decide +kernel
lemma column75_1_r4_2_eq : ∀ k : Fin 16, column75_1Expr 4 2 k = column75_1_r4_2 k := by decide +kernel
lemma column75_1_r4_3_eq : ∀ k : Fin 16, column75_1Expr 4 3 k = column75_1_r4_3 k := by decide +kernel
lemma column75_1_r4_4_eq : ∀ k : Fin 16, column75_1Expr 4 4 k = column75_1_r4_4 k := by decide +kernel
lemma column75_1_r4_5_eq : ∀ k : Fin 16, column75_1Expr 4 5 k = column75_1_r4_5 k := by decide +kernel
lemma column75_1_r4_6_eq : ∀ k : Fin 16, column75_1Expr 4 6 k = column75_1_r4_6 k := by decide +kernel
lemma column75_1_r4_7_eq : ∀ k : Fin 16, column75_1Expr 4 7 k = column75_1_r4_7 k := by decide +kernel
lemma column75_1_r4_8_eq : ∀ k : Fin 16, column75_1Expr 4 8 k = column75_1_r4_8 k := by decide +kernel
lemma column75_1_r4_9_eq : ∀ k : Fin 16, column75_1Expr 4 9 k = column75_1_r4_9 k := by decide +kernel
lemma column75_1_r4_10_eq : ∀ k : Fin 16, column75_1Expr 4 10 k = column75_1_r4_10 k := by decide +kernel
lemma column75_1_r4_11_eq : ∀ k : Fin 16, column75_1Expr 4 11 k = column75_1_r4_11 k := by decide +kernel
lemma column75_1_r4_12_eq : ∀ k : Fin 16, column75_1Expr 4 12 k = column75_1_r4_12 k := by decide +kernel
lemma column75_1_r4_13_eq : ∀ k : Fin 16, column75_1Expr 4 13 k = column75_1_r4_13 k := by decide +kernel
lemma column75_1_r4_14_eq : ∀ k : Fin 16, column75_1Expr 4 14 k = column75_1_r4_14 k := by decide +kernel
lemma column75_1_r4_15_eq : ∀ k : Fin 16, column75_1Expr 4 15 k = column75_1_r4_15 k := by decide +kernel
lemma column75_1_r4_eq (i k : Fin 16) : column75_1Expr 4 i k = column75_1_r4 i k := by
  fin_cases i
  · exact column75_1_r4_0_eq k
  · exact column75_1_r4_1_eq k
  · exact column75_1_r4_2_eq k
  · exact column75_1_r4_3_eq k
  · exact column75_1_r4_4_eq k
  · exact column75_1_r4_5_eq k
  · exact column75_1_r4_6_eq k
  · exact column75_1_r4_7_eq k
  · exact column75_1_r4_8_eq k
  · exact column75_1_r4_9_eq k
  · exact column75_1_r4_10_eq k
  · exact column75_1_r4_11_eq k
  · exact column75_1_r4_12_eq k
  · exact column75_1_r4_13_eq k
  · exact column75_1_r4_14_eq k
  · exact column75_1_r4_15_eq k
lemma column75_1_r5_0_eq : ∀ k : Fin 16, column75_1Expr 5 0 k = column75_1_r5_0 k := by decide +kernel
lemma column75_1_r5_1_eq : ∀ k : Fin 16, column75_1Expr 5 1 k = column75_1_r5_1 k := by decide +kernel
lemma column75_1_r5_2_eq : ∀ k : Fin 16, column75_1Expr 5 2 k = column75_1_r5_2 k := by decide +kernel
lemma column75_1_r5_3_eq : ∀ k : Fin 16, column75_1Expr 5 3 k = column75_1_r5_3 k := by decide +kernel
lemma column75_1_r5_4_eq : ∀ k : Fin 16, column75_1Expr 5 4 k = column75_1_r5_4 k := by decide +kernel
lemma column75_1_r5_5_eq : ∀ k : Fin 16, column75_1Expr 5 5 k = column75_1_r5_5 k := by decide +kernel
lemma column75_1_r5_6_eq : ∀ k : Fin 16, column75_1Expr 5 6 k = column75_1_r5_6 k := by decide +kernel
lemma column75_1_r5_7_eq : ∀ k : Fin 16, column75_1Expr 5 7 k = column75_1_r5_7 k := by decide +kernel
lemma column75_1_r5_8_eq : ∀ k : Fin 16, column75_1Expr 5 8 k = column75_1_r5_8 k := by decide +kernel
lemma column75_1_r5_9_eq : ∀ k : Fin 16, column75_1Expr 5 9 k = column75_1_r5_9 k := by decide +kernel
lemma column75_1_r5_10_eq : ∀ k : Fin 16, column75_1Expr 5 10 k = column75_1_r5_10 k := by decide +kernel
lemma column75_1_r5_11_eq : ∀ k : Fin 16, column75_1Expr 5 11 k = column75_1_r5_11 k := by decide +kernel
lemma column75_1_r5_12_eq : ∀ k : Fin 16, column75_1Expr 5 12 k = column75_1_r5_12 k := by decide +kernel
lemma column75_1_r5_13_eq : ∀ k : Fin 16, column75_1Expr 5 13 k = column75_1_r5_13 k := by decide +kernel
lemma column75_1_r5_14_eq : ∀ k : Fin 16, column75_1Expr 5 14 k = column75_1_r5_14 k := by decide +kernel
lemma column75_1_r5_15_eq : ∀ k : Fin 16, column75_1Expr 5 15 k = column75_1_r5_15 k := by decide +kernel
lemma column75_1_r5_eq (i k : Fin 16) : column75_1Expr 5 i k = column75_1_r5 i k := by
  fin_cases i
  · exact column75_1_r5_0_eq k
  · exact column75_1_r5_1_eq k
  · exact column75_1_r5_2_eq k
  · exact column75_1_r5_3_eq k
  · exact column75_1_r5_4_eq k
  · exact column75_1_r5_5_eq k
  · exact column75_1_r5_6_eq k
  · exact column75_1_r5_7_eq k
  · exact column75_1_r5_8_eq k
  · exact column75_1_r5_9_eq k
  · exact column75_1_r5_10_eq k
  · exact column75_1_r5_11_eq k
  · exact column75_1_r5_12_eq k
  · exact column75_1_r5_13_eq k
  · exact column75_1_r5_14_eq k
  · exact column75_1_r5_15_eq k
lemma column75_1_eq (j : Fin 6) (i k : Fin 16) : column75_1Expr j i k = column75_1 j i k := by
  fin_cases j
  · exact column75_1_r0_eq i k
  · exact column75_1_r1_eq i k
  · exact column75_1_r2_eq i k
  · exact column75_1_r3_eq i k
  · exact column75_1_r4_eq i k
  · exact column75_1_r5_eq i k
lemma column75_1_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (column75_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction true 75 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column75_1_eq,basisFunction_wave_g,← mul_assoc]
  unfold column75_1Expr
  apply CBox.contains_mul_g
  · rw [← waveAmplitude_mod true 75 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp3_1_contains j i k
  · exact power75_contains j i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.column75_1_contains_g_oai := @OAI.SharpPlanar.CachedData.column75_1_contains_g_oai
