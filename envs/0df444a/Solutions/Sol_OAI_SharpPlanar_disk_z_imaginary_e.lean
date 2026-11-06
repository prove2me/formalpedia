-- Prove2me | solution 1 for OAI.SharpPlanar.disk_z_imaginary_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:38:41.401855+00:00
-- url     : https://prove2.me/submissions/470568d1-c66e-4967-8490-df89c21aa00a

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_disk_delta_bounds_e
import Theorems.Thm_OAI_SharpPlanar_disk_denominator_ne_e
import Theorems.Thm_OAI_SharpPlanar_reciprocal_disk_bound_e

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

theorem B_pos : 0 < B := by norm_num [B]

end SharpPlanar

namespace SharpPlanar
open Complex

lemma disk_z_imaginary_e_oai {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    -(1402/17505:ℝ) ≤ (complexZ t).im := by
  let a : ℂ := (diskCenter j:ℂ)+Complex.I*(h:ℂ)
  let Δ : ℝ := Complex.normSq a-(1/6:ℝ)^2
  have hΔ : 0 < Δ := by
    have hh := (disk_delta_bounds_e hj).1
    change 167/1200 ≤ Δ at hh
    linarith
  have hΔ1 : Δ ≤ 389/400 := (disk_delta_bounds_e hj).2
  have hrec := reciprocal_disk_bound_e (a:=a) (u:=t+Complex.I*(h:ℂ))
    (by norm_num : (0:ℝ) ≤ 1/6) hΔ
    (by simpa [a] using ht) (disk_denominator_ne_e hj ht)
  have hi := (le_abs_self _).trans ((Complex.abs_im_le_norm
    ((t+Complex.I*(h:ℂ))⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a)).trans hrec)
  have haim : a.im = h := by simp [a]
  simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_im,zero_mul,add_zero,haim] at hi
  change (t+Complex.I*(h:ℂ))⁻¹.im-Δ⁻¹*(-h) ≤ (1/6)/Δ at hi
  have htop : (t+Complex.I*(h:ℂ))⁻¹.im ≤ ((1/6:ℝ)-h)/Δ := by
    rw [div_eq_mul_inv] at hi ⊢
    nlinarith only [hi]
  have heq : (complexZ t).im = -B*(t+Complex.I*(h:ℂ))⁻¹.im-h := by
    simp [complexZ,div_eq_mul_inv,Complex.mul_im]
  rw [heq]
  have hb := mul_le_mul_of_nonpos_left htop (neg_nonpos.mpr B_pos.le)
  have hq : -(1402/17505:ℝ) ≤ -B*((1/6-h)/Δ)-h := by
    have hh : (-(1402/17505:ℝ)+h)*Δ ≤ -B*(1/6-h) := by
      norm_num [B,h] at *
      nlinarith
    have hh' := (le_div_iff₀ hΔ).mpr hh
    linear_combination hh'
  linarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_z_imaginary_e_oai := @OAI.SharpPlanar.disk_z_imaginary_e_oai
