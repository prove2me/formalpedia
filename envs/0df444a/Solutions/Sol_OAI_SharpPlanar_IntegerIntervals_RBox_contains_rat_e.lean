-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.contains_rat_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:51:20.739217+00:00
-- url     : https://prove2.me/submissions/9575e0cd-1366-4b55-85d8-f3fed8941ead

import Mathlib
import Definitions.Def_OAIQ098E026
import Definitions.Def_OAIQ098E028
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_rat_check_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_rat_contains_e

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

lemma RBox.contains_rat_e_oai (m n : ℤ) (hn : 0 < n) : (RBox.rat m n).Contains ((m:ℝ)/n) :=
  RBox.rat_contains_e (RBox.rat_check_e m n hn)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.contains_rat_e_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.contains_rat_e_oai
