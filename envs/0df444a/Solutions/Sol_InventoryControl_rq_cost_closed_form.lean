-- Prove2me | solution 1 for InventoryControl.rq_cost_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T19:22:45.678175+00:00
-- url     : https://prove2.me/submissions/fc8704dc-6721-496d-8e32-8b44a7e82463

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory in
private lemma p651_pdf_eq (y : ℝ) :
    gaussianPDFReal 0 1 y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

open MeasureTheory ProbabilityTheory in
private lemma p651_pdf_fun : gaussianPDFReal 0 1
    = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  funext y; exact p651_pdf_eq y

open MeasureTheory ProbabilityTheory in
private lemma p651_pdf_cont : Continuous (gaussianPDFReal 0 1) := by
  rw [p651_pdf_fun]
  fun_prop

open MeasureTheory ProbabilityTheory in
private lemma p651_pdf_deriv (y : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-y * gaussianPDFReal 0 1 y) y := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-y) y :=
    (((hasDerivAt_pow 2 y).div_const 2).neg).congr_deriv (by norm_num)
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [p651_pdf_fun]
  exact h2.congr_deriv (by ring)

open MeasureTheory ProbabilityTheory in
private lemma p651_real_eq (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ v in s, gaussianPDFReal 0 1 v := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae (ae_of_all _ (fun _ => gaussianPDFReal_nonneg _ _ _)))]

open MeasureTheory ProbabilityTheory in
private lemma p651_cdf_deriv (y : ℝ) :
    HasDerivAt (fun u => cdf (gaussianReal 0 1) u) (gaussianPDFReal 0 1 y) y := by
  have hI : ∀ u, cdf (gaussianReal 0 1) u = ∫ v in Set.Iic u, gaussianPDFReal 0 1 v := by
    intro u; rw [cdf_eq_real, p651_real_eq]
  have hint : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have key : (fun u => cdf (gaussianReal 0 1) u)
      = fun u => cdf (gaussianReal 0 1) 0 + ∫ t in (0:ℝ)..u, gaussianPDFReal 0 1 t := by
    funext u
    rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn, hI u, hI 0]
    ring
  rw [key]
  exact ((p651_pdf_cont.integral_hasStrictDerivAt 0 y).hasDerivAt).const_add
    (cdf (gaussianReal 0 1) 0)

open MeasureTheory ProbabilityTheory in
private lemma p651_pdf_tendsto :
    Filter.Tendsto (gaussianPDFReal 0 1) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun y : ℝ => y ^ 2 / 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [mul_zero] at h
  rw [p651_pdf_fun]
  exact h

open MeasureTheory ProbabilityTheory in
private lemma p651_mul_pdf_tendsto :
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
    simp only [Function.comp, pow_one, p651_pdf_eq]
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
private lemma p651_G_closed (x : ℝ) :
    normalLoss x = gaussianPDFReal 0 1 x - x * (1 - cdf (gaussianReal 0 1) x) := by
  unfold normalLoss
  have hderiv : ∀ v ∈ Set.Ici x, HasDerivAt
      (fun v => -gaussianPDFReal 0 1 v - x * cdf (gaussianReal 0 1) v)
      ((v - x) * gaussianPDFReal 0 1 v) v := by
    intro v _
    exact ((p651_pdf_deriv v).neg.sub ((p651_cdf_deriv v).const_mul x)).congr_deriv (by ring)
  have hpos : ∀ v ∈ Set.Ioi x, 0 ≤ (v - x) * gaussianPDFReal 0 1 v := by
    intro v hv
    exact mul_nonneg (sub_nonneg.2 (le_of_lt hv)) (gaussianPDFReal_nonneg _ _ _)
  have hlim : Filter.Tendsto (fun v => -gaussianPDFReal 0 1 v - x * cdf (gaussianReal 0 1) v)
      Filter.atTop (nhds (-0 - x * 1)) :=
    (p651_pdf_tendsto.neg).sub ((tendsto_cdf_atTop (gaussianReal 0 1)).const_mul x)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  ring

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p651_G_nonneg (x : ℝ) : 0 ≤ normalLoss x := by
  unfold normalLoss
  refine setIntegral_nonneg measurableSet_Ioi ?_
  intro v hv
  exact mul_nonneg (sub_nonneg.2 (le_of_lt hv)) (gaussianPDFReal_nonneg _ _ _)


open MeasureTheory ProbabilityTheory in
private lemma p651_gauss_map (m s : ℝ) :
    gaussianReal m (Real.toNNReal (s ^ 2)) = (gaussianReal 0 1).map (fun z => s * z + m) := by
  have h : gaussianReal m (Real.toNNReal (s ^ 2))
      = ((gaussianReal 0 1).map (s * ·)).map (· + m) := by
    rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
    congr 1
    · simp
    · ext
      simp [sq_nonneg]
  rw [h, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p651_loss_std (z0 : ℝ) :
    ∫ z, max (z - z0) 0 ∂(gaussianReal 0 1) = normalLoss z0 := by
  unfold normalLoss
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_indicator measurableSet_Ioi]
  congr 1
  funext v
  simp only [Set.indicator, Set.mem_Ioi, smul_eq_mul]
  split_ifs with h
  · rw [max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith)]
    ring

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p651_loss (m s y : ℝ) (hs : 0 < s) :
    ∫ x, max (x - y) 0 ∂(gaussianReal m (Real.toNNReal (s ^ 2)))
      = s * normalLoss ((y - m) / s) := by
  rw [p651_gauss_map m s, integral_map (by fun_prop) (by fun_prop)]
  rw [← p651_loss_std, ← integral_const_mul]
  congr 1
  funext z
  rw [mul_max_of_nonneg _ _ hs.le, mul_zero]
  congr 1
  field_simp
  ring

open MeasureTheory ProbabilityTheory in
private lemma p651_int (m s y : ℝ) :
    Integrable (fun x => max (x - y) 0) (gaussianReal m (Real.toNNReal (s ^ 2))) := by
  have h : Integrable (fun x : ℝ => x) (gaussianReal m (Real.toNNReal (s ^ 2))) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  exact (h.sub (integrable_const y)).pos_part


open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p651_G_int (x : ℝ) : IntegrableOn normalLoss (Set.Ioi x) := by
  have hderiv : ∀ v ∈ Set.Ici x, HasDerivAt
      (fun v => -(((v ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) v)
        - v * gaussianPDFReal 0 1 v) / 2)) (normalLoss v) v := by
    intro v _
    have hsq : HasDerivAt (fun v : ℝ => v ^ 2 + 1) (2 * v) v :=
      ((hasDerivAt_pow 2 v).add_const 1).congr_deriv (by norm_num)
    have hA : HasDerivAt (fun u => (u ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) u))
        (2 * v * (1 - cdf (gaussianReal 0 1) v) + (v ^ 2 + 1) * (0 - gaussianPDFReal 0 1 v)) v :=
      hsq.mul ((hasDerivAt_const v (1:ℝ)).sub (p651_cdf_deriv v))
    have hB : HasDerivAt (fun u => u * gaussianPDFReal 0 1 u)
        (1 * gaussianPDFReal 0 1 v + v * (-v * gaussianPDFReal 0 1 v)) v :=
      (hasDerivAt_id' v).mul (p651_pdf_deriv v)
    refine ((hA.sub hB).div_const 2).neg.congr_deriv ?_
    rw [p651_G_closed v]
    ring
  have hpos : ∀ v ∈ Set.Ioi x, 0 ≤ normalLoss v := fun v _ => p651_G_nonneg v
  have h1 : Filter.Tendsto (fun v => (v ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) v))
      Filter.atTop (nhds 0) := by
    have hu : Filter.Tendsto (fun v => v * gaussianPDFReal 0 1 v + (1 - cdf (gaussianReal 0 1) v))
        Filter.atTop (nhds (0 + (1 - 1))) :=
      p651_mul_pdf_tendsto.add (tendsto_const_nhds.sub (tendsto_cdf_atTop (gaussianReal 0 1)))
    rw [sub_self, add_zero] at hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · filter_upwards with v
      exact mul_nonneg (by positivity) (sub_nonneg.2 (cdf_le_one _ _))
    · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with v hv
      have hG := p651_G_nonneg v
      rw [p651_G_closed v] at hG
      have hc := cdf_le_one (gaussianReal 0 1) v
      nlinarith [mul_nonneg hv (sub_nonneg.2 hG)]
  have hlim : Filter.Tendsto (fun v => -(((v ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) v)
        - v * gaussianPDFReal 0 1 v) / 2))
      Filter.atTop (nhds (-((0 - 0) / 2))) :=
    ((h1.sub p651_mul_pdf_tendsto).div_const 2).neg
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p651_H_sub (a b : ℝ) :
    normalLossH a - normalLossH b = ∫ v in a..b, normalLoss v := by
  unfold normalLossH
  exact intervalIntegral.integral_Ioi_sub_Ioi' (p651_G_int a) (p651_G_int b)

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (h b1 R Q m s : ℝ) (hh : 0 < h) (hb : 0 < b1) (hQ : 0 < Q)
    (hs : 0 < s) :
    rqCost h b1 R Q m s
      = h * (R + Q / 2 - m)
        + (h + b1) * (s ^ 2 / Q) * (normalLossH ((R - m) / s) - normalLossH ((R + Q - m) / s)) := by
  have hP : IsProbabilityMeasure (rqPosition R Q) := isProbabilityMeasure_rqPosition R Q hQ
  have hL : IsProbabilityMeasure (rqLevel R Q m s) := isProbabilityMeasure_rqLevel R Q m s hQ
  have h1 : Integrable (fun x : ℝ => x) (rqPosition R Q) := by
    unfold rqPosition ProbabilityTheory.cond
    refine Integrable.smul_measure ?_ ?_
    · exact continuous_id.integrableOn_Icc
    · simp [Real.volume_Icc, hQ]
  have h2 : Integrable (fun x : ℝ => x) (newsboyDemand m s) := by
    rw [newsboyDemand_eq]
    exact (memLp_id_gaussianReal 1).integrable le_rfl
  have hid : Integrable (fun x : ℝ => x) (rqLevel R Q m s) := by
    unfold rqLevel
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact (h1.comp_fst (newsboyDemand m s)).sub (h2.comp_snd (rqPosition R Q))
  have hneg : Integrable (fun x : ℝ => max (-x) 0) (rqLevel R Q m s) := hid.neg.pos_part
  have hpos : ∫ x, x ∂(rqPosition R Q) = R + Q / 2 := by
    unfold rqPosition ProbabilityTheory.cond
    rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), integral_id]
    simp only [Real.volume_Icc, smul_eq_mul]
    rw [show R + Q - R = Q by ring, ENNReal.toReal_inv, ENNReal.toReal_ofReal hQ.le]
    field_simp
    ring
  have hdem : ∫ x, x ∂(newsboyDemand m s) = m := by
    rw [newsboyDemand_eq]
    exact integral_id_gaussianReal
  have hmean : ∫ x, x ∂(rqLevel R Q m s) = R + Q / 2 - m := by
    unfold rqLevel
    rw [integral_map (by fun_prop) (by fun_prop)]
    rw [integral_sub (h1.comp_fst (newsboyDemand m s)) (h2.comp_snd (rqPosition R Q))]
    rw [integral_fun_fst (fun x : ℝ => x), integral_fun_snd (fun x : ℝ => x)]
    simp only [probReal_univ, one_smul, hpos, hdem]
  have hinner : ∀ y : ℝ, ∫ u, max (-(y - u)) 0 ∂(newsboyDemand m s)
      = s * normalLoss ((y - m) / s) := by
    intro y
    simp only [neg_sub, newsboyDemand_eq]
    exact p651_loss m s y hs
  have hprodint : Integrable (fun p : ℝ × ℝ => max (-(p.1 - p.2)) 0)
      ((rqPosition R Q).prod (newsboyDemand m s)) :=
    ((h1.comp_fst (newsboyDemand m s)).sub (h2.comp_snd (rqPosition R Q))).neg.pos_part
  have hback : ∫ x, max (-x) 0 ∂(rqLevel R Q m s)
      = (s ^ 2 / Q) * (normalLossH ((R - m) / s) - normalLossH ((R + Q - m) / s)) := by
    unfold rqLevel
    rw [integral_map (by fun_prop) (by fun_prop)]
    rw [integral_prod _ hprodint]
    simp only [hinner]
    unfold rqPosition ProbabilityTheory.cond
    rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul]
    simp only [sub_div]
    rw [intervalIntegral.integral_comp_div_sub normalLoss hs.ne']
    simp only [← sub_div]
    rw [← p651_H_sub]
    simp only [Real.volume_Icc, smul_eq_mul]
    rw [show R + Q - R = Q by ring, ENNReal.toReal_inv, ENNReal.toReal_ofReal hQ.le]
    field_simp
  have hpt : ∀ x : ℝ, h * max x 0 + b1 * max (-x) 0 = h * x + (h + b1) * max (-x) 0 := by
    intro x
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left hx, max_eq_right (by linarith)]
      ring
  unfold rqCost
  simp only [hpt]
  rw [integral_add (hid.const_mul h) (hneg.const_mul (h + b1)), integral_const_mul,
    integral_const_mul, hmean, hback]
  ring
