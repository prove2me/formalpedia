-- Prove2me | solution 1 for MasulloAudit.window_mellin_evaluation_bounded
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:31:06.642325+00:00
-- url     : https://prove2.me/submissions/8866af73-f67c-4cb0-9c76-93dd16c4f243

import Mathlib

set_option autoImplicit false

open MeasureTheory Set

private lemma weight_integrableOn_Iic (α c : ℝ) (h : |c| < α) :
    IntegrableOn (fun u : ℝ => Real.exp (2 * c * u - 2 * α * |u|)) (Iic 0) := by
  have h1 : 0 < 2 * c + 2 * α := by linarith [neg_abs_le c]
  refine (integrableOn_exp_mul_Iic h1 0).congr_fun (fun u hu => ?_) measurableSet_Iic
  simp only [mem_Iic] at hu
  simp only [abs_of_nonpos hu]; ring_nf

private lemma weight_integrableOn_Ioi (α c : ℝ) (h : |c| < α) :
    IntegrableOn (fun u : ℝ => Real.exp (2 * c * u - 2 * α * |u|)) (Ioi 0) := by
  have h1 : 2 * c - 2 * α < 0 := by linarith [le_abs_self c]
  refine (integrableOn_exp_mul_Ioi h1 0).congr_fun (fun u hu => ?_) measurableSet_Ioi
  simp only [mem_Ioi] at hu
  simp only [abs_of_pos hu]; ring_nf

private lemma weight_integrable (α c : ℝ) (h : |c| < α) :
    Integrable (fun u : ℝ => Real.exp (2 * c * u - 2 * α * |u|)) := by
  have := (weight_integrableOn_Iic α c h).union (weight_integrableOn_Ioi α c h)
  rwa [Iic_union_Ioi, integrableOn_univ] at this

private lemma weight_integral (α c : ℝ) (h : |c| < α) :
    ∫ u : ℝ, Real.exp (2 * c * u - 2 * α * |u|) = 1 / (2 * (α - c)) + 1 / (2 * (α + c)) := by
  have h1 : 0 < 2 * c + 2 * α := by linarith [neg_abs_le c]
  have h2 : 2 * c - 2 * α < 0 := by linarith [le_abs_self c]
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) (weight_integrableOn_Iic α c h)
    (weight_integrableOn_Ioi α c h)]
  have eL : ∫ u in Iic (0:ℝ), Real.exp (2 * c * u - 2 * α * |u|)
      = ∫ u in Iic (0:ℝ), Real.exp ((2 * c + 2 * α) * u) := by
    refine setIntegral_congr_fun measurableSet_Iic (fun u hu => ?_)
    simp only [mem_Iic] at hu
    simp only [abs_of_nonpos hu]; ring_nf
  have eR : ∫ u in Ioi (0:ℝ), Real.exp (2 * c * u - 2 * α * |u|)
      = ∫ u in Ioi (0:ℝ), Real.exp ((2 * c - 2 * α) * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    simp only [mem_Ioi] at hu
    simp only [abs_of_pos hu]; ring_nf
  rw [eL, eR, integral_exp_mul_Iic h1, integral_exp_mul_Ioi h2]
  simp only [mul_zero, Real.exp_zero]
  have ha : α - c ≠ 0 := by linarith [le_abs_self c]
  have hb : α + c ≠ 0 := by linarith [neg_abs_le c]
  have hc' : c - α ≠ 0 := by linarith [le_abs_self c]
  have hd : c + α ≠ 0 := by linarith [neg_abs_le c]
  field_simp
  ring

/-- Window Mellin evaluation is bounded on `L²(ℝ, e^{2α|u|} du)` for `|Re z| < α`. -/
theorem solution (α : ℝ) (_hα : 0 < α) (z : ℂ) (hz : |z.re| < α) :
    Integrable (fun u : ℝ => Real.exp (2 * z.re * u - 2 * α * |u|)) ∧
    (∫ u : ℝ, Real.exp (2 * z.re * u - 2 * α * |u|)) =
      1 / (2 * (α - z.re)) + 1 / (2 * (α + z.re)) ∧
    (∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (2 * z.re * u - 2 * α * |u|))) =
      ENNReal.ofReal (1 / (2 * (α - z.re)) + 1 / (2 * (α + z.re))) ∧
    ∀ g : ℝ → ℂ, Measurable g →
      (∫⁻ u : ℝ, ‖g u‖ₑ * ‖Complex.exp (z * u)‖ₑ) ^ 2 ≤
        ENNReal.ofReal (1 / (2 * (α - z.re)) + 1 / (2 * (α + z.re))) *
          ∫⁻ u : ℝ, ‖g u‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * α * |u|)) := by
  set c := z.re with hc
  have hI := weight_integrable α c hz
  have hV := weight_integral α c hz
  have hL : (∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (2 * c * u - 2 * α * |u|))) =
      ENNReal.ofReal (1 / (2 * (α - c)) + 1 / (2 * (α + c))) := by
    rw [← hV, ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))]
  refine ⟨hI, hV, hL, fun g hg => ?_⟩
  set F : ℝ → ENNReal := fun u => ‖g u‖ₑ * ENNReal.ofReal (Real.exp (α * |u|)) with hF
  set H : ℝ → ENNReal := fun u => ENNReal.ofReal (Real.exp (c * u - α * |u|)) with hH
  have hFm : AEMeasurable F volume := by
    refine (hg.enorm.mul ?_).aemeasurable
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul measurable_id.abs))
  have hHm : AEMeasurable H volume := by
    refine (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)).aemeasurable
    exact (measurable_const.mul measurable_id).sub (measurable_const.mul measurable_id.abs)
  have hold := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hFm hHm
  have eFH : ∀ u : ℝ, (F * H) u = ‖g u‖ₑ * ‖Complex.exp (z * u)‖ₑ := by
    intro u
    simp only [Pi.mul_apply, hF, hH, mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← enorm_norm,
      Complex.norm_exp, Real.enorm_eq_ofReal (Real.exp_pos _).le]
    congr 2
    simp [hc]
  have eF2 : ∀ u : ℝ, F u ^ (2:ℝ) = ‖g u‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * α * |u|)) := by
    intro u
    simp only [hF, ENNReal.rpow_two, mul_pow]
    congr 1
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have eH2 : ∀ u : ℝ, H u ^ (2:ℝ) = ENNReal.ofReal (Real.exp (2 * c * u - 2 * α * |u|)) := by
    intro u
    simp only [hH, ENNReal.rpow_two]
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  simp only [eFH, eF2, eH2, hL] at hold
  calc (∫⁻ u : ℝ, ‖g u‖ₑ * ‖Complex.exp (z * u)‖ₑ) ^ 2
      ≤ ((∫⁻ u, ‖g u‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * α * |u|))) ^ (1 / (2:ℝ)) *
          ENNReal.ofReal (1 / (2 * (α - c)) + 1 / (2 * (α + c))) ^ (1 / (2:ℝ))) ^ 2 :=
        pow_le_pow_left' hold 2
    _ = _ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      norm_num
      rw [mul_comm]
