-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.rat_check_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:40:19.537199+00:00
-- url     : https://prove2.me/submissions/fd1acdea-e4a2-4dae-aa2d-6566c5ca0067

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_rat_check_g

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

lemma CBox.rat_check_g_oai (mr nr mi ni : ℤ) (hr : 0 < nr) (hi : 0 < ni) :
    (CBox.rat mr nr mi ni).RatCheck mr nr mi ni :=
  ⟨RBox.rat_check_g _ _ hr,RBox.rat_check_g _ _ hi⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.rat_check_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.rat_check_g_oai
