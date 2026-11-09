-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.lamBox_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:44:23.263095+00:00
-- url     : https://prove2.me/submissions/d0ce82c0-4cf3-4fc6-ae20-ddc0f1c44e0d

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G092
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_inv_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

lemma denBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (denBox a).Contains ((x:ℂ)+Complex.I*(2/5:ℂ)) := by
  constructor
  · simpa [denBox] using hx
  · simpa [denBox] using RBox.contains_rat_g 2 5 (by norm_num)
lemma lamDenBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (lamDenBox a).Contains (((Real.sqrt 3/2:ℝ):ℂ)*((x:ℂ)+Complex.I*(2/5:ℂ))) :=
  CBox.contains_mul_g (rcast_contains_g bBounds_contains_g) (denBox_contains hx)
lemma lamBox_contains_g_oai {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (lamDenBox a).GoodInv) : (lamBox a).Contains (pointLambda x) := by
  have hI : (CBox.rat 0 1 1 1).Contains Complex.I := by
    simpa using CBox.contains_rat_g 0 1 1 1 (by norm_num) (by norm_num)
  simpa only [lamBox,pointLambda,div_eq_mul_inv] using
    CBox.contains_mul_g hI (CBox.contains_inv_g (lamDenBox_contains hx) hi)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.lamBox_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.lamBox_contains_g_oai
