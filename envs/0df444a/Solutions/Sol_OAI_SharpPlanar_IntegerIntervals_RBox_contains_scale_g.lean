-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.contains_scale_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:47:00.717858+00:00
-- url     : https://prove2.me/submissions/e2f7a600-c3f6-4e5f-a6aa-8544b938bc68

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_scale_check_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_scale_contains_g

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

lemma RBox.contains_scale_g_oai {a : RBox} {x : ℝ} (hx : a.Contains x) (m n : ℤ) (hn : 0 < n) :
    (a.scale m n).Contains (((m:ℝ)/n)*x) := RBox.scale_contains_g hx (RBox.scale_check_g _ _ _ hn)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.contains_scale_g_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.contains_scale_g_oai
