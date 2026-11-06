-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.mul_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:53:52.469642+00:00
-- url     : https://prove2.me/submissions/b6a068ac-8600-4328-92e9-cd7c6f4e468b

import Mathlib
import Definitions.Def_OAIQ098E028
import Definitions.Def_OAIQ098E030
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_mul_bounds_e

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

lemma precision_pos : (0:ℝ) < precision := by norm_num [precision]

lemma RBox.mul_contains_e_oai {a b c : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.MulCheck b c) : c.Contains (x*y) := by
  have hh := mul_bounds_e hx hy
  have h₁ : (c.lo:ℝ)*precision ≤ mulLo a b := by exact_mod_cast hc.1
  have h₂ : (mulHi a b:ℝ) ≤ c.hi*precision := by exact_mod_cast hc.2
  constructor
  · exact (mul_le_mul_iff_right₀ precision_pos).mp (by nlinarith only [hh.1,h₁])
  · exact (mul_le_mul_iff_right₀ precision_pos).mp (by nlinarith only [hh.2,h₂])

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.mul_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.mul_contains_e_oai
