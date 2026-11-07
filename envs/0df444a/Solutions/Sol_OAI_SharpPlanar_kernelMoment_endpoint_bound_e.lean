-- Prove2me | solution 1 for OAI.SharpPlanar.kernelMoment_endpoint_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:21:26.234658+00:00
-- url     : https://prove2.me/submissions/b554ce9c-5d4f-426e-9085-c8a879d47173

import Mathlib
import Definitions.Def_OAIQ098E125
import Theorems.Thm_OAI_SharpPlanar_endpoint_kernel_bounds_e
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_e
import Theorems.Thm_OAI_SharpPlanar_zCap_nonneg_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis

lemma kernelMoment_endpoint_bound_e_oai (j : Fin 7) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖kernelMoment ell s ((j.val:ℝ)/6)‖ ≤
      lambdaCap j*Real.exp (-Real.pi*dampingCap j*s)*(Real.pi*zCap j)^ell := by
  obtain ⟨hl,hz,hi⟩ := endpoint_kernel_bounds_e j
  have hex : ‖Complex.exp (Complex.I*Real.pi*z ((j.val:ℝ)/6)*s)‖ ≤
      Real.exp (-Real.pi*dampingCap j*s) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_sub,
      sub_zero,zero_add]
    nlinarith [mul_le_mul_of_nonneg_right hi (mul_nonneg Real.pi_pos.le hs)]
  unfold kernelMoment
  rw [norm_mul,norm_mul,norm_pow,norm_mul,norm_mul,Complex.norm_I,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul]
  have hp : (Real.pi*‖z ((j.val:ℝ)/6)‖)^ell ≤ (Real.pi*zCap j)^ell := by gcongr
  calc
    _ ≤ lambdaCap j*(Real.pi*zCap j)^ell*Real.exp (-Real.pi*dampingCap j*s) :=
      mul_le_mul (mul_le_mul hl hp (by positivity) (lambdaCap_nonneg_e _)) hex
        (norm_nonneg _) (mul_nonneg (lambdaCap_nonneg_e _) (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg_e _)) _))
    _ = _ := by ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.kernelMoment_endpoint_bound_e_oai := @OAI.SharpPlanar.kernelMoment_endpoint_bound_e_oai
