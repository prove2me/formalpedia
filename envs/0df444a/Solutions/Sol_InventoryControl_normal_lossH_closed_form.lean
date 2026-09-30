-- Prove2me | solution 1 for InventoryControl.normal_lossH_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T19:05:43.796805+00:00
-- url     : https://prove2.me/submissions/88cf2d5c-e6e7-4fa5-9af2-cdaf57f461ad

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory in
private lemma p4bf_pdf_eq (y : ℝ) :
    gaussianPDFReal 0 1 y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

open MeasureTheory ProbabilityTheory in
private lemma p4bf_pdf_fun : gaussianPDFReal 0 1
    = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  funext y; exact p4bf_pdf_eq y

open MeasureTheory ProbabilityTheory in
private lemma p4bf_pdf_cont : Continuous (gaussianPDFReal 0 1) := by
  rw [p4bf_pdf_fun]
  fun_prop

open MeasureTheory ProbabilityTheory in
private lemma p4bf_pdf_deriv (y : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-y * gaussianPDFReal 0 1 y) y := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-y) y :=
    (((hasDerivAt_pow 2 y).div_const 2).neg).congr_deriv (by norm_num)
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [p4bf_pdf_fun]
  exact h2.congr_deriv (by ring)

open MeasureTheory ProbabilityTheory in
private lemma p4bf_real_eq (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ v in s, gaussianPDFReal 0 1 v := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae (ae_of_all _ (fun _ => gaussianPDFReal_nonneg _ _ _)))]

open MeasureTheory ProbabilityTheory in
private lemma p4bf_cdf_deriv (y : ℝ) :
    HasDerivAt (fun u => cdf (gaussianReal 0 1) u) (gaussianPDFReal 0 1 y) y := by
  have hI : ∀ u, cdf (gaussianReal 0 1) u = ∫ v in Set.Iic u, gaussianPDFReal 0 1 v := by
    intro u; rw [cdf_eq_real, p4bf_real_eq]
  have hint : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have key : (fun u => cdf (gaussianReal 0 1) u)
      = fun u => cdf (gaussianReal 0 1) 0 + ∫ t in (0:ℝ)..u, gaussianPDFReal 0 1 t := by
    funext u
    rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn, hI u, hI 0]
    ring
  rw [key]
  exact ((p4bf_pdf_cont.integral_hasStrictDerivAt 0 y).hasDerivAt).const_add
    (cdf (gaussianReal 0 1) 0)

open MeasureTheory ProbabilityTheory in
private lemma p4bf_pdf_tendsto :
    Filter.Tendsto (gaussianPDFReal 0 1) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun y : ℝ => y ^ 2 / 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [mul_zero] at h
  rw [p4bf_pdf_fun]
  exact h

open MeasureTheory ProbabilityTheory in
private lemma p4bf_mul_pdf_tendsto :
    Filter.Tendsto (fun y => y * gaussianPDFReal 0 1 y) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun y : ℝ => y ^ 2 / 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ht).const_mul
    (2 * (Real.sqrt (2 * Real.pi))⁻¹)
  rw [mul_zero] at h
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
    exact mul_nonneg hy (gaussianPDFReal_nonneg _ _ _)
  · filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with y hy
    simp only [Function.comp, pow_one, p4bf_pdf_eq]
    have he : 0 ≤ Real.exp (-(y ^ 2 / 2)) := (Real.exp_pos _).le
    have hy2 : y ≤ y ^ 2 := by nlinarith
    have : y * Real.exp (-(y ^ 2 / 2)) ≤ 2 * (y ^ 2 / 2 * Real.exp (-(y ^ 2 / 2))) := by
      nlinarith
    calc y * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)))
        = (Real.sqrt (2 * Real.pi))⁻¹ * (y * Real.exp (-(y ^ 2 / 2))) := by ring
      _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (2 * (y ^ 2 / 2 * Real.exp (-(y ^ 2 / 2)))) :=
          mul_le_mul_of_nonneg_left this hc
      _ = 2 * (Real.sqrt (2 * Real.pi))⁻¹ * (y ^ 2 / 2 * Real.exp (-(y ^ 2 / 2))) := by ring

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p4bf_G_closed (x : ℝ) :
    normalLoss x = gaussianPDFReal 0 1 x - x * (1 - cdf (gaussianReal 0 1) x) := by
  unfold normalLoss
  have hderiv : ∀ v ∈ Set.Ici x, HasDerivAt
      (fun v => -gaussianPDFReal 0 1 v - x * cdf (gaussianReal 0 1) v)
      ((v - x) * gaussianPDFReal 0 1 v) v := by
    intro v _
    exact ((p4bf_pdf_deriv v).neg.sub ((p4bf_cdf_deriv v).const_mul x)).congr_deriv (by ring)
  have hpos : ∀ v ∈ Set.Ioi x, 0 ≤ (v - x) * gaussianPDFReal 0 1 v := by
    intro v hv
    exact mul_nonneg (sub_nonneg.2 (le_of_lt hv)) (gaussianPDFReal_nonneg _ _ _)
  have hlim : Filter.Tendsto (fun v => -gaussianPDFReal 0 1 v - x * cdf (gaussianReal 0 1) v)
      Filter.atTop (nhds (-0 - x * 1)) :=
    (p4bf_pdf_tendsto.neg).sub ((tendsto_cdf_atTop (gaussianReal 0 1)).const_mul x)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  ring

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p4bf_G_nonneg (x : ℝ) : 0 ≤ normalLoss x := by
  unfold normalLoss
  refine setIntegral_nonneg measurableSet_Ioi ?_
  intro v hv
  exact mul_nonneg (sub_nonneg.2 (le_of_lt hv)) (gaussianPDFReal_nonneg _ _ _)

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (x : ℝ) :
    normalLossH x
      = ((x ^ 2 + 1) * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x)
          - x * ProbabilityTheory.gaussianPDFReal 0 1 x) / 2 := by
  unfold normalLossH
  have hderiv : ∀ v ∈ Set.Ici x, HasDerivAt
      (fun v => -(((v ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) v)
        - v * gaussianPDFReal 0 1 v) / 2)) (normalLoss v) v := by
    intro v _
    have hsq : HasDerivAt (fun v : ℝ => v ^ 2 + 1) (2 * v) v :=
      ((hasDerivAt_pow 2 v).add_const 1).congr_deriv (by norm_num)
    have hA : HasDerivAt (fun u => (u ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) u))
        (2 * v * (1 - cdf (gaussianReal 0 1) v) + (v ^ 2 + 1) * (0 - gaussianPDFReal 0 1 v)) v :=
      hsq.mul ((hasDerivAt_const v (1:ℝ)).sub (p4bf_cdf_deriv v))
    have hB : HasDerivAt (fun u => u * gaussianPDFReal 0 1 u)
        (1 * gaussianPDFReal 0 1 v + v * (-v * gaussianPDFReal 0 1 v)) v :=
      (hasDerivAt_id' v).mul (p4bf_pdf_deriv v)
    refine ((hA.sub hB).div_const 2).neg.congr_deriv ?_
    rw [p4bf_G_closed v]
    ring
  have hpos : ∀ v ∈ Set.Ioi x, 0 ≤ normalLoss v := fun v _ => p4bf_G_nonneg v
  have h1 : Filter.Tendsto (fun v => (v ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) v))
      Filter.atTop (nhds 0) := by
    have hu : Filter.Tendsto (fun v => v * gaussianPDFReal 0 1 v + (1 - cdf (gaussianReal 0 1) v))
        Filter.atTop (nhds (0 + (1 - 1))) :=
      p4bf_mul_pdf_tendsto.add (tendsto_const_nhds.sub (tendsto_cdf_atTop (gaussianReal 0 1)))
    rw [sub_self, add_zero] at hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · filter_upwards with v
      exact mul_nonneg (by positivity) (sub_nonneg.2 (cdf_le_one _ _))
    · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with v hv
      have hG := p4bf_G_nonneg v
      rw [p4bf_G_closed v] at hG
      have hc := cdf_le_one (gaussianReal 0 1) v
      nlinarith [mul_nonneg hv (sub_nonneg.2 hG)]
  have hlim : Filter.Tendsto (fun v => -(((v ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) v)
        - v * gaussianPDFReal 0 1 v) / 2))
      Filter.atTop (nhds (-((0 - 0) / 2))) :=
    ((h1.sub p4bf_mul_pdf_tendsto).div_const 2).neg
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  ring
