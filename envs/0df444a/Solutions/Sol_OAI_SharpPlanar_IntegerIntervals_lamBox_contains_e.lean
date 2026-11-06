-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.lamBox_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:30:26.982636+00:00
-- url     : https://prove2.me/submissions/6baae08f-97e5-4245-9b52-62ae551f65bc

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_inv_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_ofReal_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_e

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

lemma rcast_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (rcast a).Contains (x:ℂ) := CBox.ofReal_contains_e hx
lemma denBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (denBox a).Contains ((x:ℂ)+Complex.I*(2/5:ℂ)) := by
  constructor
  · simpa [denBox] using hx
  · simpa [denBox] using RBox.contains_rat_e 2 5 (by norm_num)
lemma lamDenBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (lamDenBox a).Contains (((Real.sqrt 3/2:ℝ):ℂ)*((x:ℂ)+Complex.I*(2/5:ℂ))) :=
  CBox.contains_mul_e (rcast_contains bBounds_contains_e) (denBox_contains hx)
lemma lamBox_contains_e_oai {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (lamDenBox a).GoodInv) : (lamBox a).Contains (pointLambda x) := by
  have hI : (CBox.rat 0 1 1 1).Contains Complex.I := by
    simpa using CBox.contains_rat_e 0 1 1 1 (by norm_num) (by norm_num)
  simpa only [lamBox,pointLambda,div_eq_mul_inv] using
    CBox.contains_mul_e hI (CBox.contains_inv_e (lamDenBox_contains hx) hi)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.lamBox_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.lamBox_contains_e_oai
