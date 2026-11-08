-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.contains_rat_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:42:31.819062+00:00
-- url     : https://prove2.me/submissions/c0d9c126-7e0d-4cbe-be69-4bd91c9d259d

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_rat_check_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_rat_contains_g

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

lemma RBox.contains_rat_g_oai (m n : ℤ) (hn : 0 < n) : (RBox.rat m n).Contains ((m:ℝ)/n) :=
  RBox.rat_contains_g (RBox.rat_check_g m n hn)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.contains_rat_g_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.contains_rat_g_oai
