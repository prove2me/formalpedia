-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_left_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T19:58:21.966212+00:00
-- url     : https://prove2.me/submissions/1fa53566-9e90-4392-bba1-e4a192c11fb1

import Theorems.Thm_MasulloGRH_heckeLFunction_bounded_right_of_one
import Theorems.Thm_MasulloGRH_heckeLFunction_reflection_with_conductor
import Theorems.Thm_MasulloGRH_heckeGammaRatio_vertical_line_bound

set_option autoImplicit false

open MasulloGRH

theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C T : ℝ, ∀ t : ℝ, T ≤ |t| →
      ‖heckeLFunction χ (((-δ : ℝ) : ℂ) + t * Complex.I)‖ ≤
        C * |t| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 + δ)) := by
  obtain ⟨A, W, hA, hW, hreflection⟩ := heckeLFunction_reflection_with_conductor F χ
  obtain ⟨Treflection, hreflection⟩ := hreflection (-δ)
  obtain ⟨Cgamma, Tgamma, hCgamma, _, hgamma⟩ :=
    heckeGammaRatio_vertical_line_bound F χ (-δ)
  obtain ⟨Cright, hright⟩ := heckeLFunction_bounded_right_of_one F χ⁻¹ δ hδ
  have hCright : 0 ≤ Cright := (norm_nonneg _).trans (hright 0)
  refine ⟨A ^ (1 / 2 + δ) * Cgamma * Cright, max Treflection Tgamma, ?_⟩
  intro t ht
  let s : ℂ := ((-δ : ℝ) : ℂ) + t * Complex.I
  have hsre : s.re = -δ := by simp [s, Complex.mul_re]
  have hsim : s.im = t := by simp [s, Complex.mul_im]
  have hreflect : 1 - s = ((1 + δ : ℝ) : ℂ) + (-t : ℝ) * Complex.I := by
    apply Complex.ext <;> simp [hsre, hsim, Complex.mul_re, Complex.mul_im, sub_neg_eq_add]
  have hconductor : ‖(A : ℂ) ^ ((1 / 2 : ℂ) - s)‖ = A ^ (1 / 2 + δ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    norm_num [hsre, Complex.div_re, sub_neg_eq_add]
  have ht' : max Treflection Tgamma ≤ |s.im| := by simpa only [hsim] using ht
  have hR := hreflection s hsre ((le_max_left _ _).trans ht')
  have hG := hgamma s hsre ((le_max_right _ _).trans ht')
  rw [hsim, sub_neg_eq_add] at hG
  have hL : ‖heckeLFunction χ⁻¹ (1 - s)‖ ≤ Cright := by
    rw [hreflect]
    exact hright (-t)
  change ‖heckeLFunction χ s‖ ≤ _
  rw [hR, norm_mul, norm_mul, norm_mul, hW, one_mul, hconductor]
  have hA' := Real.rpow_nonneg hA.le (1 / 2 + δ)
  have hproduct := mul_le_mul
    (mul_le_mul_of_nonneg_left hG hA')
    hL
    (norm_nonneg _)
    (mul_nonneg hA'
      (mul_nonneg hCgamma (Real.rpow_nonneg (abs_nonneg t) _)))
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hproduct
