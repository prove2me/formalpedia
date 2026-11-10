-- Prove2me | solution 1 for OAI.SharpPlanar.kernelMoment_segment_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:21:21.015219+00:00
-- url     : https://prove2.me/submissions/2b537e8e-93c4-4863-b9b7-9c04d3a89dc5

import Mathlib
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_piece_kernel_bounds_g
import Theorems.Thm_OAI_SharpPlanar_zCap_nonneg_g

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

lemma kernelMoment_segment_bound_g_oai (j : Fin 6) (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s)
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖kernelMoment ell s t‖ ≤ segmentEnvelope j ell s t := by
  obtain ⟨hl,hz,hi⟩ := piece_kernel_bounds_g j ht
  have hex : ‖Complex.exp (Complex.I*Real.pi*z t*s)‖ ≤
      Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
      Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t)) := by
    rw [← Real.exp_add,Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_sub,
      sub_zero,zero_add]
    nlinarith [mul_le_mul_of_nonneg_right hi (mul_nonneg Real.pi_pos.le hs)]
  unfold kernelMoment segmentEnvelope
  rw [norm_mul,norm_mul,norm_pow,norm_mul,norm_mul,Complex.norm_I,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul]
  have hp : (Real.pi*‖z t‖)^ell ≤ (Real.pi*zCap ⟨j.val,by omega⟩)^ell := by
    gcongr
  calc
    _ ≤ lambdaCap ⟨j.val,by omega⟩*(Real.pi*zCap ⟨j.val,by omega⟩)^ell *
        (Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
         Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t))) :=
      mul_le_mul (mul_le_mul hl hp (by positivity) (lambdaCap_nonneg_g _)) hex
        (norm_nonneg _) (mul_nonneg (lambdaCap_nonneg_g _) (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg_g _)) _))
    _ = _ := by ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.kernelMoment_segment_bound_g_oai := @OAI.SharpPlanar.kernelMoment_segment_bound_g_oai
