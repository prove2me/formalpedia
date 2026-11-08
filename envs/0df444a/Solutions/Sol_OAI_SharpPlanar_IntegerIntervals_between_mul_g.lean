-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.between_mul_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:05:07.178852+00:00
-- url     : https://prove2.me/submissions/ad274e0d-e26e-44c2-a188-bf961d66cce8

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

namespace SharpPlanar
namespace IntegerIntervals

lemma between_mul_g_oai {a b y x L U : ℝ} (hy : a ≤ y ∧ y ≤ b)
    (ha : L ≤ x*a ∧ x*a ≤ U) (hb : L ≤ x*b ∧ x*b ≤ U) :
    L ≤ x*y ∧ x*y ≤ U := by
  rcases le_total 0 x with hx | hx
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_left hy.1 hx),
      (mul_le_mul_of_nonneg_left hy.2 hx).trans hb.2⟩
  · exact ⟨hb.1.trans (mul_le_mul_of_nonpos_left hy.2 hx),
      (mul_le_mul_of_nonpos_left hy.1 hx).trans ha.2⟩

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.between_mul_g_oai := @OAI.SharpPlanar.IntegerIntervals.between_mul_g_oai
