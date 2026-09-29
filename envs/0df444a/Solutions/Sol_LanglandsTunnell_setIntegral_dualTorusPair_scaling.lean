-- Prove2me | solution 1 for LanglandsTunnell.setIntegral_dualTorusPair_scaling
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0a6ee0f1-6d9d-5f43-8eaa-6d09a5f57b1a

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_setIntegral_dualTorusPair_scaling

set_option autoImplicit false

open MeasureTheory Set

namespace K8DS

theorem setIntegral_Iio_comp_mul_left (φ : ℝ → ℂ) {b : ℝ} (hb : 0 < b) :
    ∫ x in Iio (0 : ℝ), φ x = b • ∫ t in Iio (0 : ℝ), φ (b * t) := by
  have key : ∫ t in Iio (0 : ℝ), φ (b * t) = b⁻¹ • ∫ x in Iio (0 : ℝ), φ x := by
    rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Iio,
      ← abs_of_pos (inv_pos.mpr hb), ← Measure.integral_comp_mul_left]
    congr 1
    ext1 x
    rw [← indicator_comp_right, preimage_const_mul_Iio₀ _ hb, zero_div, Function.comp_def]
  rw [key, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]

theorem integral_comp_div_left (ψ : ℝ → ℂ) {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, ψ x = b⁻¹ • ∫ u : ℝ, ψ (u / b) := by
  rw [Measure.integral_comp_div ψ b, smul_smul, abs_of_pos hb, inv_mul_cancel₀ hb.ne', one_smul]

theorem setIntegral_Ioi_comp_inv_mul_left (χ : ℝ → ℂ) {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), χ x = b⁻¹ • ∫ Y in Ioi (0 : ℝ), χ (b⁻¹ * Y) := by
  rw [integral_comp_mul_left_Ioi χ 0 (inv_pos.mpr hb), mul_zero, inv_inv, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]

end K8DS

theorem solution
    (A₁ A₂ β γ : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y)
    (g : ℝ → ℂ) :
    (∫ a₂ in Ioi (0 : ℝ), ∫ a₁ in Iio (0 : ℝ),
        ((|a₁| : ℝ) : ℂ) ^ A₁ * ((a₂ : ℝ) : ℂ) ^ A₂ * (Real.exp (-(2 * Real.pi * (|a₁| / a₂))) : ℂ) *
        ∫ y₁ : ℝ, ∫ y₂ in Ioi (0 : ℝ),
          ((y₁⁻¹ : ℝ) : ℂ) ^ n * S y₁ * ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
            (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2 + a₂ ^ 2 * y₁ ^ 2))) : ℂ) *
            g (y₁ / y₂) *
            (∫ z : ℝ, (((a₁ * y₂ - (a₂ * y₂)⁻¹ + a₂ * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))
      = ∫ a₂ in Ioi (0 : ℝ), ∫ t in Iio (0 : ℝ), ∫ u : ℝ, ∫ Y in Ioi (0 : ℝ),
          ((a₂ : ℝ) : ℂ) ^ (A₁ + A₂ + (n : ℂ) - β - γ - 1) * (Real.exp (-(Real.pi * (a₂ ^ 2 * (u ^ 2)⁻¹))) : ℂ) *
          (((|t| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |t|)) : ℂ) *
            (((u⁻¹ : ℝ) : ℂ) ^ n * S u * ((|u| : ℝ) : ℂ) ^ β * ((Y : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + u ^ 2))) : ℂ) *
            g (u / Y) *
            (∫ z : ℝ, (((t * Y - Y⁻¹ + u : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun a₂ ha₂ => ?_)
  have ha₂' : (0 : ℝ) < a₂ := ha₂
  rw [K8DS.setIntegral_Iio_comp_mul_left _ ha₂', ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Iio (fun t ht => ?_)
  rw [K8DS.integral_comp_div_left (fun y₁ : ℝ => ∫ y₂ in Ioi (0 : ℝ), _ ) ha₂']
  rw [← integral_smul, ← integral_const_mul, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  beta_reduce
  rw [K8DS.setIntegral_Ioi_comp_inv_mul_left (fun y₂ : ℝ => _) ha₂']
  rw [← integral_smul, ← integral_smul, ← integral_const_mul, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun Y hY => ?_)
  have hY' : (0 : ℝ) < Y := hY

  have ha₂ne : a₂ ≠ 0 := ha₂'.ne'
  have hYne : Y ≠ 0 := hY'.ne'
  have ha₂c : ((a₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha₂ne
  have harg : ((a₂ : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ha₂'.le]; exact Real.pi_ne_zero.symm
  have h1 : ((|a₂ * t| : ℝ) : ℂ) ^ A₁ = ((a₂ : ℝ) : ℂ) ^ A₁ * ((|t| : ℝ) : ℂ) ^ A₁ := by
    rw [abs_mul, abs_of_pos ha₂', ← Complex.mul_cpow_ofReal_nonneg ha₂'.le (abs_nonneg t) A₁, Complex.ofReal_mul]
  have h2 : Real.exp (-(2 * Real.pi * (|a₂ * t| / a₂))) = Real.exp (-(2 * Real.pi * |t|)) := by
    rw [abs_mul, abs_of_pos ha₂', mul_div_cancel_left₀ _ ha₂ne]
  have h3 : ((u / a₂ : ℝ) : ℂ)⁻¹ ^ n = ((a₂ : ℝ) : ℂ) ^ n * ((u : ℝ) : ℂ)⁻¹ ^ n := by
    rw [Complex.ofReal_div, inv_div, div_eq_mul_inv, mul_pow]
  have h4 : S (u / a₂) = S u := hS a₂ ha₂' u
  have h5 : ((|u / a₂| : ℝ) : ℂ) ^ β = ((a₂ : ℝ) : ℂ) ^ (-β) * ((|u| : ℝ) : ℂ) ^ β := by
    rw [abs_div, abs_of_pos ha₂', div_eq_mul_inv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (abs_nonneg u) (inv_nonneg.mpr ha₂'.le), Complex.ofReal_inv,
      Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
    ring
  have h6 : (((a₂⁻¹ * Y) : ℝ) : ℂ) ^ γ = ((a₂ : ℝ) : ℂ) ^ (-γ) * ((Y : ℝ) : ℂ) ^ γ := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr ha₂'.le) hY'.le, Complex.ofReal_inv,
      Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  have e1 : ((a₂ * (a₂⁻¹ * Y)) ^ 2)⁻¹ = (Y ^ 2)⁻¹ := by rw [← mul_assoc, mul_inv_cancel₀ ha₂ne, one_mul]
  have e2 : ((u / a₂) ^ 2)⁻¹ = a₂ ^ 2 * (u ^ 2)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]
  have e3 : (a₂ * t) ^ 2 * (a₂⁻¹ * Y) ^ 2 = t ^ 2 * Y ^ 2 := by field_simp
  have e4 : a₂ ^ 2 * (u / a₂) ^ 2 = u ^ 2 := by field_simp
  have h7 : Real.exp (-(Real.pi * (((a₂ * (a₂⁻¹ * Y)) ^ 2)⁻¹ + ((u / a₂) ^ 2)⁻¹ + (a₂ * t) ^ 2 * (a₂⁻¹ * Y) ^ 2 +
        a₂ ^ 2 * (u / a₂) ^ 2)))
      = Real.exp (-(Real.pi * (a₂ ^ 2 * (u ^ 2)⁻¹))) * Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + u ^ 2))) := by
    rw [e1, e2, e3, e4, ← Real.exp_add]; congr 1; ring
  have h8 : u / a₂ / (a₂⁻¹ * Y) = u / Y := by field_simp
  have h9 : (a₂ * t * (a₂⁻¹ * Y) - (a₂ * (a₂⁻¹ * Y))⁻¹ + a₂ * (u / a₂) : ℝ) = t * Y - Y⁻¹ + u := by
    have ea : a₂ * t * (a₂⁻¹ * Y) = t * Y := by field_simp
    have eb : a₂ * (a₂⁻¹ * Y) = Y := by rw [← mul_assoc, mul_inv_cancel₀ ha₂ne, one_mul]
    have ec : a₂ * (u / a₂) = u := by field_simp
    rw [ea, eb, ec]
  have h10 : ((a₂ : ℝ) : ℂ) ^ (A₁ + A₂ + (n : ℂ) - β - γ - 1)
      = ((a₂ : ℝ) : ℂ) ^ A₁ * ((a₂ : ℝ) : ℂ) ^ A₂ * ((a₂ : ℝ) : ℂ) ^ n * ((a₂ : ℝ) : ℂ) ^ (-β) *
        ((a₂ : ℝ) : ℂ) ^ (-γ) * ((a₂ : ℝ) : ℂ)⁻¹ := by
    simp only [sub_eq_add_neg, Complex.cpow_add _ _ ha₂c, Complex.cpow_neg_one, Complex.cpow_natCast]
  have h10' : ((a₂ : ℝ) : ℂ) ^ (A₁ + A₂ + (n : ℂ) - β - γ - 1)
      = ((a₂ : ℝ) : ℂ) ^ A₁ * ((a₂ : ℝ) : ℂ) ^ A₂ * ((a₂ : ℝ) : ℂ) ^ n * ((a₂ : ℝ) : ℂ) ^ (-β) *
        ((a₂ : ℝ) : ℂ) ^ (-γ) * (((a₂ : ℝ) : ℂ) * ((((a₂ : ℝ) : ℂ))⁻¹ * (((a₂ : ℝ) : ℂ))⁻¹)) := by
    rw [mul_inv_cancel_left₀ ha₂c]; exact h10
  simp only [Complex.real_smul, Complex.ofReal_inv]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10', Complex.ofReal_mul]
  ring

end S_LanglandsTunnell_setIntegral_dualTorusPair_scaling
end P2MW
export P2MW.S_LanglandsTunnell_setIntegral_dualTorusPair_scaling (solution)
