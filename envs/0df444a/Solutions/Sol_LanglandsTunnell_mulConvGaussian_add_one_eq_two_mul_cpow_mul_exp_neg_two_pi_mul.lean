-- Prove2me | solution 1 for LanglandsTunnell.mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/33a1ecfa-3fe6-575e-9757-ab7d352e958e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Real MeasureTheory Set

namespace KcSubordination

noncomputable def E (y t : ℝ) : ℝ := rexp (-(π * (t - y / t) ^ 2))

theorem E_pos (y t : ℝ) : 0 < E y t := exp_pos _

theorem measurable_E (y : ℝ) : Measurable (E y) := by
  unfold E; fun_prop

theorem image_sub_div {y : ℝ} (hy : 0 < y) : (fun t : ℝ => t - y / t) '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun u => ?_
  set S : ℝ := √(u ^ 2 + 4 * y) with hS
  have hS0 : 0 ≤ u ^ 2 + 4 * y := by positivity
  have hSsq : S ^ 2 = u ^ 2 + 4 * y := by rw [hS, sq_sqrt hS0]
  have hSpos : 0 < S := by rw [hS]; exact sqrt_pos.2 (by positivity)
  have hSu : |u| < S := by
    rw [hS, ← sqrt_sq_eq_abs]
    exact sqrt_lt_sqrt (sq_nonneg u) (by linarith)
  have ht : 0 < (u + S) / 2 := by
    have := neg_abs_le u
    linarith
  refine ⟨(u + S) / 2, ht, ?_⟩
  have ht0 : (u + S) / 2 ≠ 0 := ht.ne'
  have h2 : y / ((u + S) / 2) = (u + S) / 2 - u := by
    rw [div_eq_iff ht0]
    linear_combination (-1 / 4 : ℝ) * hSsq
  simp only
  linarith [h2]

theorem strictMonoOn_sub_div {y : ℝ} (hy : 0 < y) : StrictMonoOn (fun t : ℝ => t - y / t) (Ioi 0) := by
  intro a ha b hb hab
  have : y / b < y / a := div_lt_div_of_pos_left hy ha hab
  simp only
  linarith

theorem hasDerivAt_sub_div (y : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => t - y / t) (1 + y / t ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => y * t⁻¹) (y * (-(t ^ 2)⁻¹)) t := (hasDerivAt_inv ht).const_mul y
  have h2 := (hasDerivAt_id t).sub h1
  convert h2 using 1
  · rfl
  · rfl
  · rfl
  ring

theorem hasDerivAt_div (y : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => y / t) (-(y / t ^ 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => y * t⁻¹) (y * (-(t ^ 2)⁻¹)) t := (hasDerivAt_inv ht).const_mul y
  convert h1 using 1 <;> first | rfl | ring1 | (field_simp; done)

theorem image_div {y : ℝ} (hy : 0 < y) : (fun t : ℝ => y / t) '' Ioi 0 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩; exact div_pos hy hr
  · intro ht
    exact ⟨y / t, div_pos hy ht, by field_simp⟩

theorem injOn_div {y : ℝ} (hy : 0 < y) : InjOn (fun t : ℝ => y / t) (Ioi 0) := by
  intro a ha b hb hab
  simp only at hab
  have ha0 : (a : ℝ) ≠ 0 := ne_of_gt ha
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb
  field_simp at hab
  nlinarith [hab]

theorem integral_W {y : ℝ} (hy : 0 < y) : ∫ t in Ioi (0:ℝ), (1 + y / t ^ 2) * E y t = 1 := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
    (f := fun t : ℝ => t - y / t) (f' := fun t => 1 + y / t ^ 2) measurableSet_Ioi
    (fun t ht => (hasDerivAt_sub_div y (ne_of_gt ht)).hasDerivWithinAt) (strictMonoOn_sub_div hy).injOn
    (fun u => rexp (-(π * u ^ 2)))
  have hg : ∫ u : ℝ, rexp (-(π * u ^ 2)) = 1 := by
    have := integral_gaussian π
    simp only [neg_mul] at this
    rw [this, div_self pi_ne_zero, sqrt_one]
  have h' : ∫ x in Ioi (0:ℝ), |1 + y / x ^ 2| • rexp (-(π * (x - y / x) ^ 2)) = 1 := by
    rw [← h, image_sub_div hy, Measure.restrict_univ, hg]
  refine Eq.trans ?_ h'
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hpos : 0 < 1 + y / t ^ 2 := by positivity
  simp only [E, smul_eq_mul, abs_of_pos hpos]

theorem integral_E_eq {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi (0:ℝ), E y t = ∫ t in Ioi (0:ℝ), y / t ^ 2 * E y t := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
    (f := fun t : ℝ => y / t) (f' := fun t => -(y / t ^ 2)) measurableSet_Ioi
    (fun t ht => (hasDerivAt_div y (ne_of_gt ht)).hasDerivWithinAt) (injOn_div hy) (E y)
  rw [image_div hy] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
  have hpos : 0 ≤ y / t ^ 2 := by positivity
  simp only [smul_eq_mul, abs_neg, abs_of_nonneg hpos, E]
  congr 2
  rw [div_div_cancel₀ hy.ne']
  ring

theorem integral_P {y : ℝ} (hy : 0 < y) : ∫ t in Ioi (0:ℝ), y / t ^ 2 * E y t = 1 / 2 := by
  have hW := integral_W hy
  have hWint : IntegrableOn (fun t => (1 + y / t ^ 2) * E y t) (Ioi 0) :=
    integrable_of_integral_eq_one hW
  have hmeasP : AEStronglyMeasurable (fun t => y / t ^ 2 * E y t) (volume.restrict (Ioi (0:ℝ))) := by
    have : Measurable (fun t => y / t ^ 2 * E y t) := by
      have := measurable_E y; fun_prop
    exact this.aestronglyMeasurable
  have hmeasE : AEStronglyMeasurable (E y) (volume.restrict (Ioi (0:ℝ))) := (measurable_E y).aestronglyMeasurable
  have hPint : IntegrableOn (fun t => y / t ^ 2 * E y t) (Ioi 0) := by
    refine Integrable.mono' hWint hmeasP (Filter.Eventually.of_forall fun t => ?_)
    have h1 : 0 ≤ y / t ^ 2 := by positivity
    have h2 : 0 < E y t := E_pos y t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2.le)]
    nlinarith
  have hEint : IntegrableOn (E y) (Ioi 0) := by
    refine Integrable.mono' hWint hmeasE (Filter.Eventually.of_forall fun t => ?_)
    have h1 : 0 ≤ y / t ^ 2 := by positivity
    have h2 : 0 < E y t := E_pos y t
    rw [Real.norm_eq_abs, abs_of_nonneg h2.le]
    nlinarith
  have hsplit : ∫ t in Ioi (0:ℝ), (1 + y / t ^ 2) * E y t =
      (∫ t in Ioi (0:ℝ), E y t) + ∫ t in Ioi (0:ℝ), y / t ^ 2 * E y t := by
    rw [← integral_add hEint hPint]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    ring
  rw [hW, integral_E_eq hy] at hsplit
  linarith

theorem glasser {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi (0:ℝ), y / t * rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2)) / t = rexp (-(2 * π * y)) / 2 := by
  have h1 : ∫ t in Ioi (0:ℝ), y / t * rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2)) / t =
      ∫ t in Ioi (0:ℝ), (y / t ^ 2 * E y t) * rexp (-(2 * π * y)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
    simp only [E]
    rw [show y / t * rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2)) / t =
      y / t ^ 2 * (rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2))) by field_simp]
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [h1, integral_mul_const, integral_P hy]
  ring

theorem discrete_eq (γ₀ : ℂ) {y : ℝ} (hy : 0 < y) :
    (4 : ℂ) * ∫ t in Ioi (0:ℝ),
        ((t : ℂ) ^ γ₀ * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (γ₀ + 1) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)
      = (2 : ℂ) • ((y : ℂ) ^ γ₀ • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)) := by
  have hcongr : ∀ t ∈ Ioi (0:ℝ),
      ((t : ℂ) ^ γ₀ * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (γ₀ + 1) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)
        = (y : ℂ) ^ γ₀ * ((y / t * rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2)) / t : ℝ) : ℂ) := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have hyt : (0:ℝ) < y / t := div_pos hy ht'
    have hne : ((y / t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hyt.ne'
    have hcp : (t : ℂ) ^ γ₀ * ((y / t : ℝ) : ℂ) ^ (γ₀ + 1) = (y : ℂ) ^ γ₀ * ((y / t : ℝ) : ℂ) := by
      rw [Complex.cpow_add _ _ hne, Complex.cpow_one, ← mul_assoc,
        ← Complex.mul_cpow_ofReal_nonneg ht'.le hyt.le, ← Complex.ofReal_mul, mul_div_cancel₀ _ ht'.ne']
    calc ((t : ℂ) ^ γ₀ * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (γ₀ + 1) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)
        = ((t : ℂ) ^ γ₀ * ((y / t : ℝ) : ℂ) ^ (γ₀ + 1)) *
            ((Real.exp (-(Real.pi * t ^ 2)) : ℂ) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ) / (t : ℂ)) := by ring
      _ = (y : ℂ) ^ γ₀ * ((y / t * rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2)) / t : ℝ) : ℂ) := by
        rw [hcp]; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul, integral_complex_ofReal, glasser hy]
  push_cast
  simp only [smul_eq_mul]
  ring

end KcSubordination

end

theorem solution
    (γ : ℂ) (y : ℝ) (hy : 0 < y) :
    (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ γ * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (γ + 1) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)
      = 2 * ((y : ℂ) ^ γ * (Real.exp (-(2 * Real.pi * y)) : ℂ)) := by
  rw [KcSubordination.discrete_eq γ hy]
  simp only [smul_eq_mul]

end S_LanglandsTunnell_mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul
end P2MW
export P2MW.S_LanglandsTunnell_mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul (solution)
