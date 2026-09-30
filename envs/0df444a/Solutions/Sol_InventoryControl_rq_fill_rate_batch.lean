-- Prove2me | solution 1 for InventoryControl.rq_fill_rate_batch
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T19:59:54.661118+00:00
-- url     : https://prove2.me/submissions/dd9d0493-4106-42f5-9605-78e004ab2679

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory in
private lemma p304r_pdf_eq (y : ℝ) :
    gaussianPDFReal 0 1 y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

open MeasureTheory ProbabilityTheory in
private lemma p304r_pdf_fun : gaussianPDFReal 0 1
    = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  funext y; exact p304r_pdf_eq y

open MeasureTheory ProbabilityTheory in
private lemma p304r_pdf_cont : Continuous (gaussianPDFReal 0 1) := by
  rw [p304r_pdf_fun]
  fun_prop

open MeasureTheory ProbabilityTheory in
private lemma p304r_pdf_deriv (y : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-y * gaussianPDFReal 0 1 y) y := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-y) y :=
    (((hasDerivAt_pow 2 y).div_const 2).neg).congr_deriv (by norm_num)
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [p304r_pdf_fun]
  exact h2.congr_deriv (by ring)

open MeasureTheory ProbabilityTheory in
private lemma p304r_real_eq (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ v in s, gaussianPDFReal 0 1 v := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae (ae_of_all _ (fun _ => gaussianPDFReal_nonneg _ _ _)))]

open MeasureTheory ProbabilityTheory in
private lemma p304r_cdf_deriv (y : ℝ) :
    HasDerivAt (fun u => cdf (gaussianReal 0 1) u) (gaussianPDFReal 0 1 y) y := by
  have hI : ∀ u, cdf (gaussianReal 0 1) u = ∫ v in Set.Iic u, gaussianPDFReal 0 1 v := by
    intro u; rw [cdf_eq_real, p304r_real_eq]
  have hint : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have key : (fun u => cdf (gaussianReal 0 1) u)
      = fun u => cdf (gaussianReal 0 1) 0 + ∫ t in (0:ℝ)..u, gaussianPDFReal 0 1 t := by
    funext u
    rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn, hI u, hI 0]
    ring
  rw [key]
  exact ((p304r_pdf_cont.integral_hasStrictDerivAt 0 y).hasDerivAt).const_add
    (cdf (gaussianReal 0 1) 0)

open MeasureTheory ProbabilityTheory in
private lemma p304r_pdf_tendsto :
    Filter.Tendsto (gaussianPDFReal 0 1) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun y : ℝ => y ^ 2 / 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [mul_zero] at h
  rw [p304r_pdf_fun]
  exact h

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p304r_G_closed (x : ℝ) :
    normalLoss x = gaussianPDFReal 0 1 x - x * (1 - cdf (gaussianReal 0 1) x) := by
  unfold normalLoss
  have hderiv : ∀ v ∈ Set.Ici x, HasDerivAt
      (fun v => -gaussianPDFReal 0 1 v - x * cdf (gaussianReal 0 1) v)
      ((v - x) * gaussianPDFReal 0 1 v) v := by
    intro v _
    exact ((p304r_pdf_deriv v).neg.sub ((p304r_cdf_deriv v).const_mul x)).congr_deriv (by ring)
  have hpos : ∀ v ∈ Set.Ioi x, 0 ≤ (v - x) * gaussianPDFReal 0 1 v := by
    intro v hv
    exact mul_nonneg (sub_nonneg.2 (le_of_lt hv)) (gaussianPDFReal_nonneg _ _ _)
  have hlim : Filter.Tendsto (fun v => -gaussianPDFReal 0 1 v - x * cdf (gaussianReal 0 1) v)
      Filter.atTop (nhds (-0 - x * 1)) :=
    (p304r_pdf_tendsto.neg).sub ((tendsto_cdf_atTop (gaussianReal 0 1)).const_mul x)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  ring

open MeasureTheory ProbabilityTheory in
private lemma p304r_cdf_cont : Continuous (cdf (gaussianReal 0 1)) := by
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
private lemma p304r_cdf_affine (m s x : ℝ) (hs : 0 < s) :
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
private lemma p304r_Ici (m s y : ℝ) (hs : 0 < s) :
    (newsboyDemand m s).real (Set.Ici y) = 1 - cdf (gaussianReal 0 1) ((y - m) / s) := by
  have hv : Real.toNNReal (s ^ 2) ≠ 0 := by simp [hs.ne']
  have := nullSingletonClass_gaussianReal (μ := m) (v := Real.toNNReal (s ^ 2)) hv
  rw [newsboyDemand_eq, ← p304r_cdf_affine m s y hs, cdf_eq_real]
  rw [measureReal_congr (Ioi_ae_eq_Ici (μ := gaussianReal m (Real.toNNReal (s ^ 2)))).symm]
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p304r_integral (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
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
    rw [h3, integral_indicator_one measurableSet_Ici, p304r_Ici m s _ hs]
  simp_rw [h2]
  unfold rqPosition ProbabilityTheory.cond
  rw [integral_smul_measure, Real.volume_Icc, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc]
  rw [add_sub_cancel_left, ENNReal.toReal_inv, ENNReal.toReal_ofReal hQ.le, smul_eq_mul]

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p304r_G_deriv (x : ℝ) :
    HasDerivAt normalLoss (cdf (gaussianReal 0 1) x - 1) x := by
  have hfun : normalLoss = fun v => gaussianPDFReal 0 1 v - v * (1 - cdf (gaussianReal 0 1) v) := by
    funext v; exact p304r_G_closed v
  rw [hfun]
  have hA : HasDerivAt (fun v => v * (1 - cdf (gaussianReal 0 1) v))
      (1 * (1 - cdf (gaussianReal 0 1) x) + x * (0 - gaussianPDFReal 0 1 x)) x :=
    (hasDerivAt_id' x).mul ((hasDerivAt_const x (1:ℝ)).sub (p304r_cdf_deriv x))
  exact ((p304r_pdf_deriv x).sub hA).congr_deriv (by ring)

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p304r_ready (R Q m s : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
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
    refine (((p304r_G_deriv ((u - m) / s)).comp u hin).const_mul (-s)).congr_deriv ?_
    rw [sub_zero]
    field_simp
    ring
  have hcont : Continuous (fun u => 1 - cdf (gaussianReal 0 1) ((u - 0 - m) / s)) :=
    continuous_const.sub (p304r_cdf_cont.comp
      (((continuous_id.sub continuous_const).sub continuous_const).div_const _))
  rw [h1, p304r_integral R Q m s 0 hQ hs,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  field_simp
  ring

open MeasureTheory ProbabilityTheory in
private lemma p304b_gauss_map (m s : ℝ) :
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
private lemma p304b_loss_std (z0 : ℝ) :
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
private lemma p304b_loss (m s y : ℝ) (hs : 0 < s) :
    ∫ x, max (x - y) 0 ∂(gaussianReal m (Real.toNNReal (s ^ 2)))
      = s * normalLoss ((y - m) / s) := by
  rw [p304b_gauss_map m s, integral_map (by fun_prop) (by fun_prop)]
  rw [← p304b_loss_std, ← integral_const_mul]
  congr 1
  funext z
  rw [mul_max_of_nonneg _ _ hs.le, mul_zero]
  congr 1
  field_simp
  ring

open MeasureTheory ProbabilityTheory in
private lemma p304b_int (m s y : ℝ) :
    Integrable (fun x => max (x - y) 0) (gaussianReal m (Real.toNNReal (s ^ 2))) := by
  have h : Integrable (fun x : ℝ => x) (gaussianReal m (Real.toNNReal (s ^ 2))) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  exact (h.sub (integrable_const y)).pos_part

private lemma p304b_pt (R Q u : ℝ) (hQ : 0 ≤ Q) :
    min (max (u - R) 0) Q = max (u - R) 0 - max (u - (R + Q)) 0 := by
  rcases le_total u R with h1 | h1
  · rw [max_eq_right (by linarith), max_eq_right (by linarith), min_eq_left hQ]
    ring
  · rcases le_total u (R + Q) with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), min_eq_left (by linarith)]
      ring
    · rw [max_eq_left (by linarith), max_eq_left (by linarith), min_eq_right (by linarith)]
      ring

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p304b_batch (R Q m s : ℝ) (hQ : 0 ≤ Q) (hs : 0 < s) :
    rqBatchBackorders R Q m s
      = s * normalLoss ((R - m) / s) - s * normalLoss ((R + Q - m) / s) := by
  unfold rqBatchBackorders newsboyDemand
  simp_rw [p304b_pt R Q _ hQ]
  rw [integral_sub (p304b_int m s R) (p304b_int m s (R + Q)), p304b_loss m s R hs,
    p304b_loss m s (R + Q) hs]

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (R Q m s : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    1 - rqBatchBackorders R Q m s / Q = rqReadyRate R Q m s := by
  rw [p304b_batch R Q m s hQ.le hs, p304r_ready R Q m s hQ hs]
  field_simp
