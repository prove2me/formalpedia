-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_rat_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:12:58.397448+00:00
-- url     : https://prove2.me/submissions/6c6faf8a-e79d-4712-bb99-6134fca8bdcc

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_rat_check_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_rat_contains_g

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

lemma CBox.contains_rat_g_oai (mr nr mi ni : ℤ) (hr : 0 < nr) (hi : 0 < ni) :
    (CBox.rat mr nr mi ni).Contains ((mr:ℂ)/nr+(mi:ℂ)/ni*Complex.I) :=
  CBox.rat_contains_g (CBox.rat_check_g _ _ _ _ hr hi)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_rat_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_rat_g_oai
