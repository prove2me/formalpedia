-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.mul_bounds_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:49:51.009984+00:00
-- url     : https://prove2.me/submissions/5c4aa72c-ab51-42ce-bc62-055bc9285e3d

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_real_mul_bounds_g

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

lemma mul_bounds_g_oai {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (mulLo a b:ℝ) ≤ (precision:ℝ)^2*(x*y) ∧
      (precision:ℝ)^2*(x*y) ≤ (mulHi a b:ℝ) := by
  convert real_mul_bounds_g hx hy using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast [mulLo,mulHi] <;> ring_nf)

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.mul_bounds_g_oai := @OAI.SharpPlanar.IntegerIntervals.mul_bounds_g_oai
