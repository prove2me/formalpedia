-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.mul_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:49:48.725042+00:00
-- url     : https://prove2.me/submissions/2c8db29a-5cc8-453d-ad87-c73299e5e235

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_mul_bounds_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g

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

lemma RBox.mul_contains_g_oai {a b c : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.MulCheck b c) : c.Contains (x*y) := by
  have hh := mul_bounds_g hx hy
  have h₁ : (c.lo:ℝ)*precision ≤ mulLo a b := by exact_mod_cast hc.1
  have h₂ : (mulHi a b:ℝ) ≤ c.hi*precision := by exact_mod_cast hc.2
  constructor
  · exact (mul_le_mul_iff_right₀ precision_pos_g).mp (by nlinarith only [hh.1,h₁])
  · exact (mul_le_mul_iff_right₀ precision_pos_g).mp (by nlinarith only [hh.2,h₂])

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.mul_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.mul_contains_g_oai
