-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.inv_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:52:47.613378+00:00
-- url     : https://prove2.me/submissions/72f94671-7c04-40e4-986d-beea5caefb4e

import Mathlib
import Definitions.Def_OAIQ098E028
import Definitions.Def_OAIQ098E030

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

lemma RBox.inv_contains_e_oai {a c : RBox} {x : ℝ} (hx : a.Contains x)
    (hc : a.InvCheck c) : c.Contains x⁻¹ := by
  have ha : (0:ℝ) < a.lo := by exact_mod_cast hc.1
  have hcl : (0:ℝ) ≤ c.lo := by exact_mod_cast hc.2.1
  have hcu : (0:ℝ) ≤ c.hi := by exact_mod_cast hc.2.2.1
  have h₁ : (c.lo:ℝ)*a.hi ≤ (precision:ℝ)^2 := by exact_mod_cast hc.2.2.2.1
  have h₂ : (precision:ℝ)^2 ≤ (c.hi:ℝ)*a.lo := by exact_mod_cast hc.2.2.2.2
  have hp := precision_pos
  have hx0 : 0 < x := by nlinarith only [hx.1,ha,hp]
  constructor <;> rw [← div_eq_mul_inv]
  · apply (le_div_iff₀ hx0).mpr
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [mul_le_mul_of_nonneg_left hx.2 hcl,h₁]
  · apply (div_le_iff₀ hx0).mpr
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [mul_le_mul_of_nonneg_left hx.1 hcu,h₂]


end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.inv_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.inv_contains_e_oai
