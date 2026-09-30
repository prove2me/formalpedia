-- Prove2me | solution 1 for InventoryControl.rq_cost_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T19:50:44.261842+00:00
-- url     : https://prove2.me/submissions/b9d5b2c5-89d4-4d22-b332-a9b8027606be

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory in
private lemma pf6f_pdf_eq (y : ℝ) :
    gaussianPDFReal 0 1 y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

open MeasureTheory ProbabilityTheory in
private lemma pf6f_pdf_fun : gaussianPDFReal 0 1
    = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  funext y; exact pf6f_pdf_eq y

open MeasureTheory ProbabilityTheory in
private lemma pf6f_pdf_cont : Continuous (gaussianPDFReal 0 1) := by
  rw [pf6f_pdf_fun]
  fun_prop

open MeasureTheory ProbabilityTheory in
private lemma pf6f_pdf_deriv (y : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-y * gaussianPDFReal 0 1 y) y := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-y) y :=
    (((hasDerivAt_pow 2 y).div_const 2).neg).congr_deriv (by norm_num)
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [pf6f_pdf_fun]
  exact h2.congr_deriv (by ring)

open MeasureTheory ProbabilityTheory in
private lemma pf6f_real_eq (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ v in s, gaussianPDFReal 0 1 v := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae (ae_of_all _ (fun _ => gaussianPDFReal_nonneg _ _ _)))]

open MeasureTheory ProbabilityTheory in
private lemma pf6f_cdf_deriv (y : ℝ) :
    HasDerivAt (fun u => cdf (gaussianReal 0 1) u) (gaussianPDFReal 0 1 y) y := by
  have hI : ∀ u, cdf (gaussianReal 0 1) u = ∫ v in Set.Iic u, gaussianPDFReal 0 1 v := by
    intro u; rw [cdf_eq_real, pf6f_real_eq]
  have hint : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have key : (fun u => cdf (gaussianReal 0 1) u)
      = fun u => cdf (gaussianReal 0 1) 0 + ∫ t in (0:ℝ)..u, gaussianPDFReal 0 1 t := by
    funext u
    rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn, hI u, hI 0]
    ring
  rw [key]
  exact ((pf6f_pdf_cont.integral_hasStrictDerivAt 0 y).hasDerivAt).const_add
    (cdf (gaussianReal 0 1) 0)

open MeasureTheory ProbabilityTheory in
private lemma pf6f_pdf_tendsto :
    Filter.Tendsto (gaussianPDFReal 0 1) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun y : ℝ => y ^ 2 / 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [mul_zero] at h
  rw [pf6f_pdf_fun]
  exact h

open MeasureTheory ProbabilityTheory in
private lemma pf6f_mul_pdf_tendsto :
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
    simp only [Function.comp, pow_one, pf6f_pdf_eq]
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
private lemma pf6f_G_closed (x : ℝ) :
    normalLoss x = gaussianPDFReal 0 1 x - x * (1 - cdf (gaussianReal 0 1) x) := by
  unfold normalLoss
  have hderiv : ∀ v ∈ Set.Ici x, HasDerivAt
      (fun v => -gaussianPDFReal 0 1 v - x * cdf (gaussianReal 0 1) v)
      ((v - x) * gaussianPDFReal 0 1 v) v := by
    intro v _
    exact ((pf6f_pdf_deriv v).neg.sub ((pf6f_cdf_deriv v).const_mul x)).congr_deriv (by ring)
  have hpos : ∀ v ∈ Set.Ioi x, 0 ≤ (v - x) * gaussianPDFReal 0 1 v := by
    intro v hv
    exact mul_nonneg (sub_nonneg.2 (le_of_lt hv)) (gaussianPDFReal_nonneg _ _ _)
  have hlim : Filter.Tendsto (fun v => -gaussianPDFReal 0 1 v - x * cdf (gaussianReal 0 1) v)
      Filter.atTop (nhds (-0 - x * 1)) :=
    (pf6f_pdf_tendsto.neg).sub ((tendsto_cdf_atTop (gaussianReal 0 1)).const_mul x)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  ring

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_G_nonneg (x : ℝ) : 0 ≤ normalLoss x := by
  unfold normalLoss
  refine setIntegral_nonneg measurableSet_Ioi ?_
  intro v hv
  exact mul_nonneg (sub_nonneg.2 (le_of_lt hv)) (gaussianPDFReal_nonneg _ _ _)


open MeasureTheory ProbabilityTheory in
private lemma pf6f_gauss_map (m s : ℝ) :
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
private lemma pf6f_loss_std (z0 : ℝ) :
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
private lemma pf6f_loss (m s y : ℝ) (hs : 0 < s) :
    ∫ x, max (x - y) 0 ∂(gaussianReal m (Real.toNNReal (s ^ 2)))
      = s * normalLoss ((y - m) / s) := by
  rw [pf6f_gauss_map m s, integral_map (by fun_prop) (by fun_prop)]
  rw [← pf6f_loss_std, ← integral_const_mul]
  congr 1
  funext z
  rw [mul_max_of_nonneg _ _ hs.le, mul_zero]
  congr 1
  field_simp
  ring

open MeasureTheory ProbabilityTheory in
private lemma pf6f_int (m s y : ℝ) :
    Integrable (fun x => max (x - y) 0) (gaussianReal m (Real.toNNReal (s ^ 2))) := by
  have h : Integrable (fun x : ℝ => x) (gaussianReal m (Real.toNNReal (s ^ 2))) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  exact (h.sub (integrable_const y)).pos_part


open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_G_int (x : ℝ) : IntegrableOn normalLoss (Set.Ioi x) := by
  have hderiv : ∀ v ∈ Set.Ici x, HasDerivAt
      (fun v => -(((v ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) v)
        - v * gaussianPDFReal 0 1 v) / 2)) (normalLoss v) v := by
    intro v _
    have hsq : HasDerivAt (fun v : ℝ => v ^ 2 + 1) (2 * v) v :=
      ((hasDerivAt_pow 2 v).add_const 1).congr_deriv (by norm_num)
    have hA : HasDerivAt (fun u => (u ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) u))
        (2 * v * (1 - cdf (gaussianReal 0 1) v) + (v ^ 2 + 1) * (0 - gaussianPDFReal 0 1 v)) v :=
      hsq.mul ((hasDerivAt_const v (1:ℝ)).sub (pf6f_cdf_deriv v))
    have hB : HasDerivAt (fun u => u * gaussianPDFReal 0 1 u)
        (1 * gaussianPDFReal 0 1 v + v * (-v * gaussianPDFReal 0 1 v)) v :=
      (hasDerivAt_id' v).mul (pf6f_pdf_deriv v)
    refine ((hA.sub hB).div_const 2).neg.congr_deriv ?_
    rw [pf6f_G_closed v]
    ring
  have hpos : ∀ v ∈ Set.Ioi x, 0 ≤ normalLoss v := fun v _ => pf6f_G_nonneg v
  have h1 : Filter.Tendsto (fun v => (v ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) v))
      Filter.atTop (nhds 0) := by
    have hu : Filter.Tendsto (fun v => v * gaussianPDFReal 0 1 v + (1 - cdf (gaussianReal 0 1) v))
        Filter.atTop (nhds (0 + (1 - 1))) :=
      pf6f_mul_pdf_tendsto.add (tendsto_const_nhds.sub (tendsto_cdf_atTop (gaussianReal 0 1)))
    rw [sub_self, add_zero] at hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · filter_upwards with v
      exact mul_nonneg (by positivity) (sub_nonneg.2 (cdf_le_one _ _))
    · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with v hv
      have hG := pf6f_G_nonneg v
      rw [pf6f_G_closed v] at hG
      have hc := cdf_le_one (gaussianReal 0 1) v
      nlinarith [mul_nonneg hv (sub_nonneg.2 hG)]
  have hlim : Filter.Tendsto (fun v => -(((v ^ 2 + 1) * (1 - cdf (gaussianReal 0 1) v)
        - v * gaussianPDFReal 0 1 v) / 2))
      Filter.atTop (nhds (-((0 - 0) / 2))) :=
    ((h1.sub pf6f_mul_pdf_tendsto).div_const 2).neg
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_H_sub (a b : ℝ) :
    normalLossH a - normalLossH b = ∫ v in a..b, normalLoss v := by
  unfold normalLossH
  exact intervalIntegral.integral_Ioi_sub_Ioi' (pf6f_G_int a) (pf6f_G_int b)

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_closed (h b1 R Q m s : ℝ) (hh : 0 < h) (hb : 0 < b1) (hQ : 0 < Q)
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
    exact pf6f_loss m s y hs
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
    rw [← pf6f_H_sub]
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


open MeasureTheory ProbabilityTheory in
private lemma pf6f_cdf_cont : Continuous (cdf (gaussianReal 0 1)) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hmono : Monotone (cdf (gaussianReal 0 1)) := monotone_cdf _
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hr : Function.rightLim (cdf (gaussianReal 0 1)) a = cdf (gaussianReal 0 1) a :=
    ((cdf (gaussianReal 0 1)).right_continuous a).rightLim_eq
  have hl : Function.leftLim (cdf (gaussianReal 0 1)) a = cdf (gaussianReal 0 1) a := by
    have h1 := (cdf (gaussianReal 0 1)).measure_singleton a
    rw [measure_cdf] at h1
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    have h0 : gaussianReal 0 1 {a} = 0 := measure_singleton a
    rw [h0] at h1
    have h2 := hmono.leftLim_le (le_refl a)
    have h3 := ENNReal.ofReal_eq_zero.1 h1.symm
    linarith
  rw [hl, hr]

open MeasureTheory ProbabilityTheory in
private lemma pf6f_cdf_affine (m s x : ℝ) (hs : 0 < s) :
    cdf (gaussianReal m (Real.toNNReal (s ^ 2))) x = cdf (gaussianReal 0 1) ((x - m) / s) := by
  have hmap : gaussianReal m (Real.toNNReal (s ^ 2))
      = ((gaussianReal 0 1).map (s * ·)).map (· + m) := by
    rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
    congr 1
    · simp
    · ext
      simp [sq_nonneg]
  rw [cdf_eq_real, cdf_eq_real, hmap, Measure.map_map (by fun_prop) (by fun_prop)]
  rw [measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext z
  simp only [Set.mem_preimage, Function.comp, Set.mem_Iic]
  rw [le_div_iff₀ hs]
  constructor <;> intro h <;> linarith

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_Ici (m s y : ℝ) (hs : 0 < s) :
    (newsboyDemand m s).real (Set.Ici y) = 1 - cdf (gaussianReal 0 1) ((y - m) / s) := by
  have hv : Real.toNNReal (s ^ 2) ≠ 0 := by simp [hs.ne']
  have := nullSingletonClass_gaussianReal (μ := m) (v := Real.toNNReal (s ^ 2)) hv
  rw [newsboyDemand_eq, ← pf6f_cdf_affine m s y hs, cdf_eq_real]
  rw [measureReal_congr (Ioi_ae_eq_Ici (μ := gaussianReal m (Real.toNNReal (s ^ 2)))).symm]
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_integral (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    rqCDF R Q m s x
      = Q⁻¹ * ∫ u in R..R + Q, (1 - cdf (gaussianReal 0 1) ((u - x - m) / s)) := by
  have hP : IsProbabilityMeasure (rqPosition R Q) := isProbabilityMeasure_rqPosition R Q hQ
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 - p.2 ≤ x} :=
    measurableSet_le (by fun_prop) measurable_const
  have h1 : rqCDF R Q m s x = ((rqPosition R Q).prod (newsboyDemand m s)).real
      {p : ℝ × ℝ | p.1 - p.2 ≤ x} := by
    unfold rqCDF rqLevel
    rw [measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  rw [h1, ← integral_indicator_one hS]
  rw [integral_prod _ (by exact (integrable_const (1:ℝ)).indicator hS)]
  have h2 : ∀ u : ℝ, ∫ d, ({p : ℝ × ℝ | p.1 - p.2 ≤ x}.indicator 1 (u, d) : ℝ)
      ∂(newsboyDemand m s) = 1 - cdf (gaussianReal 0 1) ((u - x - m) / s) := by
    intro u
    have h3 : (fun d => ({p : ℝ × ℝ | p.1 - p.2 ≤ x}.indicator 1 (u, d) : ℝ))
        = (Set.Ici (u - x)).indicator 1 := by
      funext d
      simp only [Set.indicator, Set.mem_ofPred_eq, Set.mem_Ici, Pi.one_apply]
      congr 1
      apply propext
      constructor <;> intro h <;> linarith
    rw [h3, integral_indicator_one measurableSet_Ici, pf6f_Ici m s _ hs]
  simp_rw [h2]
  unfold rqPosition ProbabilityTheory.cond
  rw [integral_smul_measure, Real.volume_Icc, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc]
  rw [add_sub_cancel_left, ENNReal.toReal_inv, ENNReal.toReal_ofReal hQ.le, smul_eq_mul]


open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_G_deriv (x : ℝ) :
    HasDerivAt normalLoss (cdf (gaussianReal 0 1) x - 1) x := by
  have hfun : normalLoss = fun v => gaussianPDFReal 0 1 v - v * (1 - cdf (gaussianReal 0 1) v) := by
    funext v; exact pf6f_G_closed v
  rw [hfun]
  have hA : HasDerivAt (fun v => v * (1 - cdf (gaussianReal 0 1) v))
      (1 * (1 - cdf (gaussianReal 0 1) x) + x * (0 - gaussianPDFReal 0 1 x)) x :=
    (hasDerivAt_id' x).mul ((hasDerivAt_const x (1:ℝ)).sub (pf6f_cdf_deriv x))
  exact ((pf6f_pdf_deriv x).sub hA).congr_deriv (by ring)

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_G_cont : Continuous normalLoss :=
  continuous_iff_continuousAt.2 fun x => (pf6f_G_deriv x).continuousAt

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_H_deriv (x : ℝ) :
    HasDerivAt normalLossH (-normalLoss x) x := by
  have hfun : normalLossH = fun t => normalLossH 0 - ∫ v in (0:ℝ)..t, normalLoss v := by
    funext t
    rw [← pf6f_H_sub]
    ring
  rw [hfun]
  exact ((pf6f_G_cont.integral_hasStrictDerivAt 0 x).hasDerivAt).const_sub (normalLossH 0)

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_ready (R Q m s : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    rqReadyRate R Q m s
      = 1 - s / Q * (normalLoss ((R - m) / s) - normalLoss ((R + Q - m) / s)) := by
  have hL : IsProbabilityMeasure (rqLevel R Q m s) := isProbabilityMeasure_rqLevel R Q m s hQ
  have h1 : rqReadyRate R Q m s = 1 - rqCDF R Q m s 0 := by
    unfold rqReadyRate rqCDF
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  have hderiv : ∀ u ∈ Set.uIcc R (R + Q), HasDerivAt (fun u => -s * normalLoss ((u - m) / s))
      (1 - cdf (gaussianReal 0 1) ((u - 0 - m) / s)) u := by
    intro u _
    have hin : HasDerivAt (fun u : ℝ => (u - m) / s) (1 / s) u :=
      ((hasDerivAt_id u).sub_const m).div_const s
    refine (((pf6f_G_deriv ((u - m) / s)).comp u hin).const_mul (-s)).congr_deriv ?_
    rw [sub_zero]
    field_simp
    ring
  have hcont : Continuous (fun u => 1 - cdf (gaussianReal 0 1) ((u - 0 - m) / s)) :=
    continuous_const.sub (pf6f_cdf_cont.comp
      (((continuous_id.sub continuous_const).sub continuous_const).div_const _))
  rw [h1, pf6f_integral R Q m s 0 hQ hs,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  field_simp
  ring

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_deriv (h b1 R Q m s : ℝ) (hh : 0 < h) (hb : 0 < b1) (hQ : 0 < Q) (hs : 0 < s) :
    HasDerivAt (fun R => rqCost h b1 R Q m s) (-b1 + (h + b1) * rqReadyRate R Q m s) R := by
  have hfun : (fun R => rqCost h b1 R Q m s) = fun R => h * (R + Q / 2 - m)
      + (h + b1) * (s ^ 2 / Q) * (normalLossH ((R - m) / s) - normalLossH ((R + Q - m) / s)) := by
    funext R'
    exact pf6f_closed h b1 R' Q m s hh hb hQ hs
  rw [hfun, pf6f_ready R Q m s hQ hs]
  have hin1 : HasDerivAt (fun u : ℝ => (u - m) / s) (1 / s) R :=
    ((hasDerivAt_id R).sub_const m).div_const s
  have hin2 : HasDerivAt (fun u : ℝ => (u + Q - m) / s) (1 / s) R :=
    (((hasDerivAt_id R).add_const Q).sub_const m).div_const s
  have hA := (pf6f_H_deriv ((R - m) / s)).comp R hin1
  have hB := (pf6f_H_deriv ((R + Q - m) / s)).comp R hin2
  have hlin : HasDerivAt (fun u : ℝ => h * (u + Q / 2 - m)) h R :=
    ((((hasDerivAt_id R).add_const (Q / 2)).sub_const m).const_mul h).congr_deriv (by simp)
  refine (hlin.add ((hA.sub hB).const_mul ((h + b1) * (s ^ 2 / Q)))).congr_deriv ?_
  field_simp
  ring

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma pf6f_ready_mono (Q m s : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    Monotone (fun R => rqReadyRate R Q m s) := by
  have hfun : (fun R => rqReadyRate R Q m s)
      = fun R => 1 - s / Q * (normalLoss ((R - m) / s) - normalLoss ((R + Q - m) / s)) := by
    funext R
    exact pf6f_ready R Q m s hQ hs
  have hk : Antitone (fun R => normalLoss ((R - m) / s) - normalLoss ((R + Q - m) / s)) := by
    refine antitone_of_hasDerivAt_nonpos (f' := fun R =>
      (cdf (gaussianReal 0 1) ((R - m) / s) - 1) * (1 / s)
        - (cdf (gaussianReal 0 1) ((R + Q - m) / s) - 1) * (1 / s)) ?_ ?_
    · intro R
      have hin1 : HasDerivAt (fun u : ℝ => (u - m) / s) (1 / s) R :=
        ((hasDerivAt_id R).sub_const m).div_const s
      have hin2 : HasDerivAt (fun u : ℝ => (u + Q - m) / s) (1 / s) R :=
        (((hasDerivAt_id R).add_const Q).sub_const m).div_const s
      exact ((pf6f_G_deriv ((R - m) / s)).comp R hin1).sub
        ((pf6f_G_deriv ((R + Q - m) / s)).comp R hin2)
    · intro R
      have hle : (R - m) / s ≤ (R + Q - m) / s := div_le_div_of_nonneg_right (by linarith) hs.le
      have hc := monotone_cdf (gaussianReal 0 1) hle
      have hs' : 0 < 1 / s := by positivity
      simp only [Pi.zero_apply]
      nlinarith
  rw [hfun]
  intro a b hab
  have h1 := hk hab
  have hsq : 0 < s / Q := div_pos hs hQ
  simp only
  nlinarith

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (h b1 Q m s : ℝ) (hh : 0 < h) (hb : 0 < b1) (hQ : 0 < Q) (hs : 0 < s) :
    ConvexOn ℝ Set.univ (fun R => rqCost h b1 R Q m s) := by
  have hd : ∀ R, HasDerivAt (fun R => rqCost h b1 R Q m s)
      (-b1 + (h + b1) * rqReadyRate R Q m s) R :=
    fun R => pf6f_deriv h b1 R Q m s hh hb hQ hs
  have hderiv : deriv (fun R => rqCost h b1 R Q m s)
      = fun R => -b1 + (h + b1) * rqReadyRate R Q m s := by
    funext R
    exact (hd R).deriv
  refine Monotone.convexOn_univ_of_deriv (fun R => (hd R).differentiableAt) ?_
  rw [hderiv]
  intro a b hab
  have h1 := pf6f_ready_mono Q m s hQ hs hab
  have hc : 0 < h + b1 := by linarith
  simp only at h1 ⊢
  nlinarith
