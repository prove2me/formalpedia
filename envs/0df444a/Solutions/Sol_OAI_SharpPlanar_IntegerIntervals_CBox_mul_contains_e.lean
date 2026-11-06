-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.mul_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:24:39.787435+00:00
-- url     : https://prove2.me/submissions/3786bdfe-6889-44cc-8260-f0a4cc81eec4

import Mathlib
import Definitions.Def_OAIQ098E031
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

lemma CBox.mul_contains_e_oai {a b c : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.MulCheck b c) : c.Contains (x*y) := by
  have hrr := mul_bounds_e hx.1 hy.1
  have hri := mul_bounds_e hx.1 hy.2
  have hir := mul_bounds_e hx.2 hy.1
  have hii := mul_bounds_e hx.2 hy.2
  have h₁ : (c.re.lo:ℝ)*precision ≤ (mulLo a.re b.re:ℝ)-(mulHi a.im b.im:ℝ) := by exact_mod_cast hc.1
  have h₂ : (mulHi a.re b.re:ℝ)-(mulLo a.im b.im:ℝ) ≤ (c.re.hi:ℝ)*precision := by exact_mod_cast hc.2.1
  have h₃ : (c.im.lo:ℝ)*precision ≤ (mulLo a.re b.im:ℝ)+(mulLo a.im b.re:ℝ) := by exact_mod_cast hc.2.2.1
  have h₄ : (mulHi a.re b.im:ℝ)+(mulHi a.im b.re:ℝ) ≤ (c.im.hi:ℝ)*precision := by exact_mod_cast hc.2.2.2
  constructor <;> constructor
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_re]
    nlinarith only [hrr.1,hii.2,h₁]
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_re]
    nlinarith only [hrr.2,hii.1,h₂]
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_im]
    nlinarith only [hri.1,hir.1,h₃]
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_im]
    nlinarith only [hri.2,hir.2,h₄]


end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.mul_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.mul_contains_e_oai
