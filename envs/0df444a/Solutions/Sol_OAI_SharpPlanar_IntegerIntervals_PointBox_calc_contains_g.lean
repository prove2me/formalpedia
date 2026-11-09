-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:07:14.270777+00:00
-- url     : https://prove2.me/submissions/8f965018-e0a2-4253-8164-19710a968a3b

import Mathlib
import Definitions.Def_OAIQ098G090
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G093
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_exp_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_lamBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_quarterArgBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_zBox_contains_g

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

lemma directArgBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (directArgBox a).Contains (-Complex.I*Real.pi*x) := by
  simpa only [directArgBox,neg_mul] using CBox.neg_contains_g (CBox.contains_mul_g piI_contains_g (rcast_contains_g hx))

lemma PointBox.calc_contains_g_oai {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hc : PointBox.Check a) : (PointBox.calc a).Contains x := by
  exact ⟨hx,lamBox_contains_g hx hc.2.1,zBox_contains_g hx hc.1,
    CBox.contains_exp_g (directArgBox_contains hx) 3 hc.2.2.1,
    CBox.contains_exp_g (quarterArgBox_contains_g hx hc.1) 3 hc.2.2.2⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_g_oai
