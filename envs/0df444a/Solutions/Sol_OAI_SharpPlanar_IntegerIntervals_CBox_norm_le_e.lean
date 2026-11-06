-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:26:12.109912+00:00
-- url     : https://prove2.me/submissions/b5ce21e0-4d75-4f76-8c18-92475626ac95

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_e

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

lemma CBox.norm_le_e_oai {a : CBox} {z : ℂ} {n : ℤ} (hz : a.Contains z) (hc : a.NormCheck n) :
    ‖z‖ ≤ (n:ℝ) := by
  have h₁ := RBox.abs_bound_e hz.1
  have h₂ := RBox.abs_bound_e hz.2
  have hc' : (a.re.bound:ℝ)+a.im.bound ≤ (precision:ℝ)*n := by exact_mod_cast hc
  have hh := mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im z) precision_pos.le
  apply (mul_le_mul_iff_right₀ precision_pos).mp
  nlinarith only [h₁,h₂,hc',hh]

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_e_oai
