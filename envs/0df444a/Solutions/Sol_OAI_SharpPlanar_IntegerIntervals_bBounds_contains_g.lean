-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.bBounds_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:49:05.54438+00:00
-- url     : https://prove2.me/submissions/5275b49f-9d01-4be5-bb61-aa0d91bf550f

import Mathlib
import Definitions.Def_OAIQ098G059
import Definitions.Def_OAIQ098G083

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

namespace SharpPlanar
namespace IntegerIntervals

lemma bBounds_contains_g_oai : bBounds.Contains (Real.sqrt 3/2) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  norm_num [bBounds,RBox.Contains,precision]
  constructor <;> nlinarith

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.bBounds_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.bBounds_contains_g_oai
