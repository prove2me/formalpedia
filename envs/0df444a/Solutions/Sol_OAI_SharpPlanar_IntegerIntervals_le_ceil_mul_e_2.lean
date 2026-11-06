-- Prove2me | solution 2 for OAI.SharpPlanar.IntegerIntervals.le_ceil_mul_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T05:28:35.895617+00:00
-- url     : https://prove2.me/submissions/f3d63cf2-3686-4d47-ac1b-a5a43f0144b2

import Mathlib
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_floor_mul_le_e

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

lemma le_ceil_mul_e_oai (x : ℤ) {n : ℤ} (hn : 0 < n) : x ≤ -((-x)/n)*n := by
  have hh := floor_mul_le_e (-x) hn
  nlinarith only [hh]

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.le_ceil_mul_e_oai := @OAI.SharpPlanar.IntegerIntervals.le_ceil_mul_e_oai
