-- Prove2me | solution 1 for OAI.SharpPlanar.Pmoment_norm_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:24:31.78611+00:00
-- url     : https://prove2.me/submissions/74bb95fd-fa85-4dad-9632-9c067ba7cce8

import Mathlib
import Definitions.Def_OAIQ098G362
import Definitions.Def_OAIQ098G1642
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_atomicCoefficient_norm_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_DirectBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Direct spectral estimates

The norm of the direct spectral kernel gives derivative bounds for cardinal functions.
-/

namespace SharpPlanar
open MeasureTheory Set IntegerBasis
open scoped BigOperators
lemma directKernel_norm (ell : ℕ) (s t : ℝ) :
    ‖directKernel ell s t‖=(Real.pi*|t|)^ell := by
  unfold directKernel
  rw [norm_mul,norm_pow,norm_mul,norm_mul,Complex.norm_I,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_exp]
  have he : (Complex.I*Real.pi*(t:ℂ)*s).re=0 := by simp
  rw [he,Real.exp_zero,mul_one]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Envelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral derivative bounds

Monotone spectral envelopes bound the cardinal functions and their Fourier kernels.
The estimates follow *A sharp Fourier certificate for planar circle packing*
(OpenAI, 2026).
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma Pmoment_norm_bound_g_oai (ell : ℕ) (s : ℝ) : |Pmoment ell s| ≤ 25*Real.pi^ell := by
  have he : Pmoment ell s=(∑ j : Fin 7,atomicCoefficient j*directKernel ell s ((j.val:ℝ)/6)).re := by
    norm_num [Pmoment,atomicCoefficient,directKernel,Fin.sum_univ_succ,Finset.sum_Icc_succ_top]
    ring
  rw [he]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : Fin 7,atomMass j*Real.pi^ell := by
      apply Finset.sum_le_sum; intro j _
      rw [norm_mul,atomicCoefficient_norm_g,directKernel_norm,abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left
      · apply pow_le_pow_left₀ (by positivity)
        have hj : (j.val:ℝ) ≤ 6 := by exact_mod_cast (by omega : j.val ≤ 6)
        nlinarith [Real.pi_pos]
      · fin_cases j <;> (first | (simp [atomMass]; all_goals first | (norm_num [atomMass]; done) | rfl | decide) | (norm_num [atomMass]; done) | norm_num [atomMass])
    _=25*Real.pi^ell := by rw [← Finset.sum_mul]; norm_num [atomMass,Fin.sum_univ_succ]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Pmoment_norm_bound_g_oai := @OAI.SharpPlanar.Pmoment_norm_bound_g_oai
