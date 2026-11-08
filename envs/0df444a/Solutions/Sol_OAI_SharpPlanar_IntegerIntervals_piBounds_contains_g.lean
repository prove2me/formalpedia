-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.piBounds_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:51:15.492552+00:00
-- url     : https://prove2.me/submissions/2d4f59c2-c7de-4c9f-a3a7-6ba461a41502

import Mathlib
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

lemma piBounds_contains_g_oai : piBounds.Contains Real.pi := by
  have hp := Real.pi_gt_d20
  have hq := Real.pi_lt_d20
  norm_num [piBounds,RBox.Contains,precision]
  constructor <;> linarith

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.piBounds_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.piBounds_contains_g_oai
