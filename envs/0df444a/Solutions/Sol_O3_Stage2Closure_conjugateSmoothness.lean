-- Prove2me | solution 1 for O3.Stage2Closure.conjugateSmoothness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:42:25.802779+00:00
-- url     : https://prove2.me/submissions/41c8323f-c8f3-4e66-8b6f-1feff8260e4c

import Definitions.Def_O3_Stage2RouteA
import Definitions.Def_O3_Stage2RouteB
import Mathlib.Analysis.Convex.Deriv
import Definitions.Def_O3_Stage2BelowGeometry
import Theorems.Thm_O3_Stage2Closure_squaredLpEnergy_two_smooth
import Theorems.Thm_O3_Stage2Closure_squaredLpEnergy_smooth_above_two
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_conjugateExponent_eq
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.Stage2RouteD.dualityMap_zero
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open O3
open O3.Stage2Closure
open scoped BigOperators
open Stage2RouteA Stage2RouteB
namespace O3.Stage2Closure
theorem _root_.solution : ConjugateSmoothnessStatement := by
  intro p hp hp2 d u v
  by_cases hpEq : p = 2
  · subst p
    norm_num [conjugateExponent_eq]
    simpa only [show ((2 : ℝ) - 1) / 2 = 1 / 2 by norm_num] using
      squaredLpEnergy_two_smooth u v
  · have hpLt : p < 2 := lt_of_le_of_ne hp2 hpEq
    have hq : 2 < conjugateExponent p := by
      rw [conjugateExponent_eq, lt_div_iff₀ (by linarith : 0 < p - 1)]
      linarith
    exact squaredLpEnergy_smooth_above_two hq u v
end O3.Stage2Closure
