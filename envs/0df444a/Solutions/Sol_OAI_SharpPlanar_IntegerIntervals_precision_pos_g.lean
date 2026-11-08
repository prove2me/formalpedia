-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.precision_pos_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:07:29.819095+00:00
-- url     : https://prove2.me/submissions/2bb5289f-2af9-444d-a25d-6e725125b79b

import Mathlib
import Definitions.Def_OAIQ098G017

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

lemma precision_pos_g_oai : (0:ℝ) < precision := by norm_num [precision]

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.precision_pos_g_oai := @OAI.SharpPlanar.IntegerIntervals.precision_pos_g_oai
