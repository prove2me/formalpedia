-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.bBounds_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:56:05.98712+00:00
-- url     : https://prove2.me/submissions/b222791e-f984-4e35-af31-9e2e15f6b7e7

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

lemma bBounds_contains_e_oai : bBounds.Contains (Real.sqrt 3/2) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  norm_num [bBounds,RBox.Contains,precision]
  constructor <;> nlinarith

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.bBounds_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.bBounds_contains_e_oai
