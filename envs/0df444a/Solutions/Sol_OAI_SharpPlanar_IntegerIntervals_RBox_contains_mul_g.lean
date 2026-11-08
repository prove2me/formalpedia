-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.contains_mul_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:38:32.526367+00:00
-- url     : https://prove2.me/submissions/3e1c7465-5002-4903-9a8a-c7b746cc9ab9

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_check_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_contains_g

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

lemma RBox.contains_mul_g_oai {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := RBox.mul_contains_g hx hy (RBox.mul_check_g _ _)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.contains_mul_g_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.contains_mul_g_oai
