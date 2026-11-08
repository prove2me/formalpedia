-- Prove2me | solution 1 for OAI.SharpPlanar.reciprocal_disk_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:07:09.744572+00:00
-- url     : https://prove2.me/submissions/6ddfb2d7-c630-4d47-b12b-f854d9d2d76d

import Mathlib
import Theorems.Thm_OAI_SharpPlanar_reciprocal_disk_identity_g

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

lemma reciprocal_disk_bound_g_oai {a u : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hΔ : 0 < Complex.normSq a-r^2) (hu : ‖u-a‖ ≤ r) (hu0 : u ≠ 0) :
    ‖u⁻¹-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a‖ ≤ r/(Complex.normSq a-r^2) := by
  let Δ := Complex.normSq a-r^2
  have hid := reciprocal_disk_identity_g a u⁻¹ r (ne_of_gt hΔ)
  have he : (1:ℂ)-a*u⁻¹ = (u-a)*u⁻¹ := by field_simp
  rw [he,Complex.normSq_mul,Complex.normSq_eq_norm_sq (u-a)] at hid
  have hnon : 0 ≤ Complex.normSq u⁻¹ := Complex.normSq_nonneg _
  have hsmall : Complex.normSq a-r^2 > 0 := hΔ
  have hprod : (‖u-a‖^2-r^2)*Complex.normSq u⁻¹ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (u-a)]) hnon
  rw [Complex.normSq_eq_norm_sq (u⁻¹-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a)] at hid
  have hdpos : 0 < Δ := hΔ
  have hdne : Δ ≠ 0 := ne_of_gt hdpos
  have hratio : 0 ≤ r/Δ := div_nonneg hr hdpos.le
  have hn := norm_nonneg (u⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a)
  have hsq : ‖u⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a‖^2 ≤ (r/Δ)^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hdpos)).mp
    have heq : Δ^2*(r/Δ)^2 = r^2 := by field_simp
    rw [heq]
    have hprod' : Δ*‖u⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a‖^2 ≤ r^2/Δ := by
      dsimp [Δ]
      nlinarith only [hid,hprod]
    have hh := mul_le_mul_of_nonneg_left hprod' hdpos.le
    have heq' : Δ*(r^2/Δ) = r^2 := by field_simp
    rw [heq'] at hh
    nlinarith only [hh]
  dsimp [Δ] at *
  nlinarith only [hsq, hn, hratio]


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.reciprocal_disk_bound_g_oai := @OAI.SharpPlanar.reciprocal_disk_bound_g_oai
