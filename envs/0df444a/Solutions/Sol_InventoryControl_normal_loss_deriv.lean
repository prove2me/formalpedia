-- Prove2me | solution 1 for InventoryControl.normal_loss_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T18:16:37.501557+00:00
-- url     : https://prove2.me/submissions/d94a687a-af1c-48e9-a786-5b17bd62d2d8

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p2ec_loss_std (z0 : ℝ) :
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
lemma p2ec_int_pos (y : ℝ) :
    Integrable (fun x : ℝ => max (x - y) 0) (gaussianReal 0 1) :=
  (((memLp_id_gaussianReal 1).integrable le_rfl).sub (integrable_const y)).pos_part

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p2ec_subgrad (a z : ℝ) :
    (cdf (gaussianReal 0 1) a - 1) * (z - a) ≤ normalLoss z - normalLoss a := by
  have hP : (gaussianReal 0 1).real (Set.Ioi a) = 1 - cdf (gaussianReal 0 1) a := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real]
  have hz := p2ec_int_pos z
  have ha := p2ec_int_pos a
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
  rw [hint, p2ec_loss_std, p2ec_loss_std] at hle
  nlinarith

lemma p2ec_hasDerivAt_of_subgrad (g p : ℝ → ℝ) (y : ℝ)
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
lemma p2ec_cdf_cont : Continuous (cdf (gaussianReal 0 1)) := by
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
theorem solution (x : ℝ) :
    HasDerivAt normalLoss (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x - 1) x := by
  exact p2ec_hasDerivAt_of_subgrad normalLoss (fun a => cdf (gaussianReal 0 1) a - 1) x
    (fun a z => p2ec_subgrad a z) (p2ec_cdf_cont.sub continuous_const).continuousAt
