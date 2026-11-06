-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_rat_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:23:05.791207+00:00
-- url     : https://prove2.me/submissions/40c30b7f-abfc-47f6-b713-45b4e19d8c18

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_rat_check_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_rat_contains_e

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

lemma CBox.contains_rat_e_oai (mr nr mi ni : ℤ) (hr : 0 < nr) (hi : 0 < ni) :
    (CBox.rat mr nr mi ni).Contains ((mr:ℂ)/nr+(mi:ℂ)/ni*Complex.I) :=
  CBox.rat_contains_e (CBox.rat_check_e _ _ _ _ hr hi)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_rat_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_rat_e_oai
