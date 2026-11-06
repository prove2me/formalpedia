-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:28:31.375236+00:00
-- url     : https://prove2.me/submissions/3e684a75-c6a8-4dfc-93f8-173873c4fda2

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_exp_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_neg_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_ofReal_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_lamBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_quarterArgBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_zBox_contains_e

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
lemma directArgBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (directArgBox a).Contains (-Complex.I*Real.pi*x) := by
  simpa only [directArgBox,neg_mul] using CBox.neg_contains_e (CBox.contains_mul_e piI_contains_e (rcast_contains hx))

lemma PointBox.calc_contains_e_oai {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hc : PointBox.Check a) : (PointBox.calc a).Contains x := by
  exact ⟨hx,lamBox_contains_e hx hc.2.1,zBox_contains_e hx hc.1,
    CBox.contains_exp_e (directArgBox_contains hx) 3 hc.2.2.1,
    CBox.contains_exp_e (quarterArgBox_contains_e hx hc.1) 3 hc.2.2.2⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_e_oai
