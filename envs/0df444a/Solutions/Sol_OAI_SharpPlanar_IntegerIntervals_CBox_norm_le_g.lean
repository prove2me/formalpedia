-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:07:40.13441+00:00
-- url     : https://prove2.me/submissions/279d3dde-2062-4bd2-80a9-403e1544ea00

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_g
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

lemma CBox.norm_le_g_oai {a : CBox} {z : ℂ} {n : ℤ} (hz : a.Contains z) (hc : a.NormCheck n) :
    ‖z‖ ≤ (n:ℝ) := by
  have h₁ := RBox.abs_bound_g hz.1
  have h₂ := RBox.abs_bound_g hz.2
  have hc' : (a.re.bound:ℝ)+a.im.bound ≤ (precision:ℝ)*n := by exact_mod_cast hc
  have hh := mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im z) precision_pos_g.le
  apply (mul_le_mul_iff_right₀ precision_pos_g).mp
  nlinarith only [h₁,h₂,hc',hh]

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_g_oai
