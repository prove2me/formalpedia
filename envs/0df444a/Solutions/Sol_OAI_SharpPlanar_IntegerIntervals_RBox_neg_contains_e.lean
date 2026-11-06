-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.neg_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:54:14.787972+00:00
-- url     : https://prove2.me/submissions/1f6628a2-f445-4ebe-8386-52b8a8df4446

import Mathlib
import Definitions.Def_OAIQ098E028

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

lemma RBox.neg_contains_e_oai {a : RBox} {x : ℝ} (hx : a.Contains x) : a.neg.Contains (-x) := by
  simpa [Contains,neg,mul_neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.neg_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.neg_contains_e_oai
