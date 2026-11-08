-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.le_ceil_mul_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:05:24.428273+00:00
-- url     : https://prove2.me/submissions/c370f13c-4851-4251-8f71-be34756ae87c

import Mathlib
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_floor_mul_le_g

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

lemma le_ceil_mul_g_oai (x : ℤ) {n : ℤ} (hn : 0 < n) : x ≤ -((-x)/n)*n := by
  have hh := floor_mul_le_g (-x) hn
  nlinarith only [hh]

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.le_ceil_mul_g_oai := @OAI.SharpPlanar.IntegerIntervals.le_ceil_mul_g_oai
