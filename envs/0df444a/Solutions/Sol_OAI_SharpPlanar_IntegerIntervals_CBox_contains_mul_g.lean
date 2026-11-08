-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_mul_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:09:41.368539+00:00
-- url     : https://prove2.me/submissions/6dc166a9-3065-4777-b5d7-474a586cbaa2

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_mul_check_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_mul_contains_g

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

lemma CBox.contains_mul_g_oai {a b : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := CBox.mul_contains_g hx hy (CBox.mul_check_g _ _)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_mul_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_mul_g_oai
