-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.zBox_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:35:18.745069+00:00
-- url     : https://prove2.me/submissions/cd61764c-a4f2-4add-8c15-4e13df6d17bc

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G089
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_inv_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g

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
lemma zBox_contains_g_oai {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (denBox a).GoodInv) : (zBox a).Contains (pointZ x) := by
  have hc : (CBox.rat 0 1 (-2) 5).Contains (-Complex.I*(2/5:ℂ)) := by
    convert CBox.contains_rat_g 0 1 (-2) 5 (by norm_num) (by norm_num) using 1 <;> first | rfl | ring
  have hh := CBox.contains_add_g
    (CBox.contains_scale_g (CBox.contains_inv_g (denBox_contains hx) hi) (-4) 3 (by norm_num)) hc
  unfold zBox
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [pointZ,div_eq_mul_inv,sub_eq_add_neg]
  ring

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.zBox_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.zBox_contains_g_oai
