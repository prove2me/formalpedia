-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.rat_check_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:13:32.339648+00:00
-- url     : https://prove2.me/submissions/d39f276c-eebc-44b0-9dc5-7a19f161836d

import Mathlib
import Definitions.Def_OAIQ098E026
import Definitions.Def_OAIQ098E030
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_rat_check_e

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

lemma CBox.rat_check_e_oai (mr nr mi ni : ℤ) (hr : 0 < nr) (hi : 0 < ni) :
    (CBox.rat mr nr mi ni).RatCheck mr nr mi ni :=
  ⟨RBox.rat_check_e _ _ hr,RBox.rat_check_e _ _ hi⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.rat_check_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.rat_check_e_oai
