-- Prove2me | solution 1 for InventoryControl.rq_cdf_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T19:39:06.244624+00:00
-- url     : https://prove2.me/submissions/6f6403c1-80a9-4e64-82cf-63488f248bd0

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory in
private lemma p918_cdf_affine (m s x : ℝ) (hs : 0 < s) :
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
private lemma p918_Ici (m s y : ℝ) (hs : 0 < s) :
    (newsboyDemand m s).real (Set.Ici y) = 1 - cdf (gaussianReal 0 1) ((y - m) / s) := by
  have hv : Real.toNNReal (s ^ 2) ≠ 0 := by simp [hs.ne']
  have := nullSingletonClass_gaussianReal (μ := m) (v := Real.toNNReal (s ^ 2)) hv
  rw [newsboyDemand_eq, ← p918_cdf_affine m s y hs, cdf_eq_real]
  rw [measureReal_congr (Ioi_ae_eq_Ici (μ := gaussianReal m (Real.toNNReal (s ^ 2)))).symm]
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p918_integral (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
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
    rw [h3, integral_indicator_one measurableSet_Ici, p918_Ici m s _ hs]
  simp_rw [h2]
  unfold rqPosition ProbabilityTheory.cond
  rw [integral_smul_measure, Real.volume_Icc, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc]
  rw [add_sub_cancel_left, ENNReal.toReal_inv, ENNReal.toReal_ofReal hQ.le, smul_eq_mul]

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p918_loss_std (z0 : ℝ) :
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

open MeasureTheory ProbabilityTheory in
private lemma p918_int_pos (y : ℝ) :
    Integrable (fun x : ℝ => max (x - y) 0) (gaussianReal 0 1) :=
  (((memLp_id_gaussianReal 1).integrable le_rfl).sub (integrable_const y)).pos_part

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p918_subgrad (a z : ℝ) :
    (cdf (gaussianReal 0 1) a - 1) * (z - a) ≤ normalLoss z - normalLoss a := by
  have hP : (gaussianReal 0 1).real (Set.Ioi a) = 1 - cdf (gaussianReal 0 1) a := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real]
  have hz := p918_int_pos z
  have ha := p918_int_pos a
  have hind : Integrable (fun x : ℝ => (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x)
      (gaussianReal 0 1) :=
    ((integrable_const (1:ℝ)).indicator measurableSet_Ioi).const_mul _
  have hle : ∫ x, max (x - a) 0 ∂(gaussianReal 0 1)
      + ∫ x, (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x ∂(gaussianReal 0 1)
      ≤ ∫ x, max (x - z) 0 ∂(gaussianReal 0 1) := by
    rw [← integral_add ha hind]
    apply integral_mono (ha.add hind) hz
    intro x
    show max (x - a) 0 + (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x ≤ max (x - z) 0
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ x - a)]
      have := le_max_left (x - z) 0
      linarith
    · rw [max_eq_right (by linarith : x - a ≤ 0)]
      have := le_max_right (x - z) 0
      linarith
  have hint : ∫ x, (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x ∂(gaussianReal 0 1)
      = (a - z) * (1 - cdf (gaussianReal 0 1) a) := by
    rw [integral_const_mul, integral_indicator_const _ measurableSet_Ioi, hP, smul_eq_mul, mul_one]
  rw [hint, p918_loss_std, p918_loss_std] at hle
  nlinarith

private lemma p918_hasDerivAt_of_subgrad (g p : ℝ → ℝ) (y : ℝ)
    (hsub : ∀ a z, p a * (z - a) ≤ g z - g a) (hp : ContinuousAt p y) :
    HasDerivAt g (p y) y := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ z in nhds y, |p z - p y| < c := by
    have hball := hp (Metric.ball_mem_nhds (p y) hc)
    filter_upwards [hball] with z hz
    have hz' : dist (p z) (p y) < c := hz
    rwa [Real.dist_eq] at hz'
  filter_upwards [hev] with z hz
  have h1 := hsub y z
  have h2 := hsub z y
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
  rw [abs_le]
  have h3 : (p z - p y) * (z - y) ≤ |p z - p y| * |z - y| := by
    rw [← abs_mul]; exact le_abs_self _
  have h4 : |p z - p y| * |z - y| ≤ c * |z - y| :=
    mul_le_mul_of_nonneg_right hz.le (abs_nonneg _)
  have h5 : 0 ≤ c * |z - y| := mul_nonneg hc.le (abs_nonneg _)
  constructor
  · nlinarith
  · nlinarith

open MeasureTheory ProbabilityTheory in
private lemma p918_cdf_cont : Continuous (cdf (gaussianReal 0 1)) := by
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

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p918_loss_deriv (y : ℝ) :
    HasDerivAt normalLoss (cdf (gaussianReal 0 1) y - 1) y :=
  p918_hasDerivAt_of_subgrad normalLoss (fun a => cdf (gaussianReal 0 1) a - 1) y
    (fun a z => p918_subgrad a z) (p918_cdf_cont.sub continuous_const).continuousAt

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p918_ftc (R Q m s x : ℝ) (hs : 0 < s) :
    ∫ u in R..R + Q, (1 - cdf (gaussianReal 0 1) ((u - x - m) / s))
      = s * (normalLoss ((R - x - m) / s) - normalLoss ((R + Q - x - m) / s)) := by
  have hderiv : ∀ u ∈ Set.uIcc R (R + Q),
      HasDerivAt (fun u => -(s * normalLoss ((u - x - m) / s)))
        (1 - cdf (gaussianReal 0 1) ((u - x - m) / s)) u := by
    intro u _
    have hin : HasDerivAt (fun u : ℝ => (u - x - m) / s) (1 / s) u :=
      (((hasDerivAt_id u).sub_const x).sub_const m).div_const s
    have hc := (p918_loss_deriv ((u - x - m) / s)).comp u hin
    have hd := (hc.const_mul s).neg
    refine hd.congr_deriv ?_
    field_simp
    ring
  have hcont : Continuous (fun u : ℝ => 1 - cdf (gaussianReal 0 1) ((u - x - m) / s)) :=
    continuous_const.sub (p918_cdf_cont.comp (by fun_prop))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  ring

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    rqCDF R Q m s x
      = s / Q * (normalLoss ((R - x - m) / s) - normalLoss ((R + Q - x - m) / s)) := by
  rw [p918_integral R Q m s x hQ hs, p918_ftc R Q m s x hs]
  field_simp
