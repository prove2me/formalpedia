-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.contains_add_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T16:44:07.329201+00:00
-- url     : https://prove2.me/submissions/9c8d686b-1770-44af-ab81-6aaa21d092c9

import Mathlib
import Definitions.Def_OAIQ098E028
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_check_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_contains_e

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

lemma RBox.contains_add_e_oai {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := RBox.add_contains_e hx hy (RBox.add_check_e _ _)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.contains_add_e_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.contains_add_e_oai
