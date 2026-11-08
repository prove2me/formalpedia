-- Prove2me | solution 1 for OAI.SharpPlanar.phase_exp_norm_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:44.401947+00:00
-- url     : https://prove2.me/submissions/6f37af21-2f03-42bc-8edf-e9adf142827e

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open Complex

lemma phase_exp_norm_bound_g_oai {w : ℂ} {m L : ℝ} (hm : 0 ≤ m) (hw : -L ≤ w.im) :
    ‖Complex.exp (Complex.I*Real.pi*w*m)‖ ≤ Real.exp (Real.pi*m*L) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,
    zero_sub,sub_zero,zero_add]
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hm) (show 0 ≤ w.im+L by linarith)]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.phase_exp_norm_bound_g_oai := @OAI.SharpPlanar.phase_exp_norm_bound_g_oai
