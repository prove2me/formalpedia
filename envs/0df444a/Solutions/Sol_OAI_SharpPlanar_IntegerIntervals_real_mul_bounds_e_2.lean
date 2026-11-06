-- Prove2me | solution 2 for OAI.SharpPlanar.IntegerIntervals.real_mul_bounds_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T05:28:36.516085+00:00
-- url     : https://prove2.me/submissions/de043d1c-a3f4-4b01-babf-c85a5ec7e628

import Mathlib
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_between_mul_e

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

lemma real_mul_bounds_e_oai {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  apply between_mul_e hy
  · rw [mul_comm x c]
    apply between_mul_e hx <;> constructor <;> simp only [mul_comm c, le_max_iff, min_le_iff, le_refl] <;> tauto
  · rw [mul_comm x d]
    apply between_mul_e hx <;> constructor <;> simp only [mul_comm d, le_max_iff, min_le_iff, le_refl] <;> tauto

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.real_mul_bounds_e_oai := @OAI.SharpPlanar.IntegerIntervals.real_mul_bounds_e_oai
