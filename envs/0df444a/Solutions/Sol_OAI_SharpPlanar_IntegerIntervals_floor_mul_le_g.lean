-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.floor_mul_le_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:05:12.042857+00:00
-- url     : https://prove2.me/submissions/1e492f08-ff21-4417-82a1-6c0dedde2c8a

import Mathlib

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

lemma floor_mul_le_g_oai (x : ℤ) {n : ℤ} (hn : 0 < n) : x/n*n ≤ x :=
  Int.ediv_mul_le x (ne_of_gt hn)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.floor_mul_le_g_oai := @OAI.SharpPlanar.IntegerIntervals.floor_mul_le_g_oai
