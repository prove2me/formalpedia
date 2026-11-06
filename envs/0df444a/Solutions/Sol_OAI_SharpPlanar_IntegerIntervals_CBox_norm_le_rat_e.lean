-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_rat_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:50:40.982744+00:00
-- url     : https://prove2.me/submissions/df761a58-3654-409d-9248-d2ba802a787c

import Mathlib
import Definitions.Def_OAIQ098E092
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

end IntegerIntervals
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerIntervals

lemma CBox.norm_le_rat_e_oai {a : CBox} {z : ℂ} {m n : ℤ} (hz : a.Contains z)
    (hc : a.SqNormCheck m n) : ‖z‖ ≤ (m:ℝ)/n := by
  have hn : (0:ℝ) < n := by exact_mod_cast hc.1
  have hm : (0:ℝ) ≤ m := by exact_mod_cast hc.2.1
  have hr := RBox.abs_bound_e hz.1
  have hi := RBox.abs_bound_e hz.2
  have hb1 : (0:ℝ) ≤ a.re.bound := (mul_nonneg precision_pos.le (abs_nonneg _)).trans hr
  have hb2 : (0:ℝ) ≤ a.im.bound := (mul_nonneg precision_pos.le (abs_nonneg _)).trans hi
  have hs1 : (precision:ℝ)^2*z.re^2 ≤ (a.re.bound:ℝ)^2 := by
    simpa only [mul_pow, sq_abs] using
      (sq_le_sq₀ (mul_nonneg precision_pos.le (abs_nonneg _)) hb1).mpr hr
  have hs2 : (precision:ℝ)^2*z.im^2 ≤ (a.im.bound:ℝ)^2 := by
    simpa only [mul_pow, sq_abs] using
      (sq_le_sq₀ (mul_nonneg precision_pos.le (abs_nonneg _)) hb2).mpr hi
  have hh : (((a.re.bound:ℝ)^2+(a.im.bound:ℝ)^2)*(n:ℝ)^2) ≤ ((precision:ℝ)*m)^2 := by
    exact_mod_cast hc.2.2
  have he : ‖z‖^2 = z.re^2+z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  have hk : ((precision:ℝ)*‖z‖)^2 ≤ (a.re.bound:ℝ)^2+(a.im.bound:ℝ)^2 := by
    rw [mul_pow,he]; nlinarith only [hs1,hs2]
  have hkn := mul_le_mul_of_nonneg_right hk (sq_nonneg (n:ℝ))
  have hbound : (‖z‖*(n:ℝ))^2 ≤ (m:ℝ)^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos precision_pos)).mp
    nlinarith only [hkn,hh]
  apply (le_div_iff₀ hn).mpr
  nlinarith only [hbound,mul_nonneg (norm_nonneg z) hn.le,hm]

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_rat_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_rat_e_oai
