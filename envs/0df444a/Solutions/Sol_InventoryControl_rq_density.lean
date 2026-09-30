-- Prove2me | solution 1 for InventoryControl.rq_density
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T19:17:51.78716+00:00
-- url     : https://prove2.me/submissions/9d088834-3c9c-4387-a824-1f8063b1dbb9

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory in
private lemma p4e4_cdf_cont : Continuous (cdf (gaussianReal 0 1)) := by
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
private lemma p4e4_cdf_affine (m s x : ℝ) (hs : 0 < s) :
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
private lemma p4e4_Ici (m s y : ℝ) (hs : 0 < s) :
    (newsboyDemand m s).real (Set.Ici y) = 1 - cdf (gaussianReal 0 1) ((y - m) / s) := by
  have hv : Real.toNNReal (s ^ 2) ≠ 0 := by simp [hs.ne']
  have := nullSingletonClass_gaussianReal (μ := m) (v := Real.toNNReal (s ^ 2)) hv
  rw [newsboyDemand_eq, ← p4e4_cdf_affine m s y hs, cdf_eq_real]
  rw [measureReal_congr (Ioi_ae_eq_Ici (μ := gaussianReal m (Real.toNNReal (s ^ 2)))).symm]
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p4e4_integral (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
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
    rw [h3, integral_indicator_one measurableSet_Ici, p4e4_Ici m s _ hs]
  simp_rw [h2]
  unfold rqPosition ProbabilityTheory.cond
  rw [integral_smul_measure, Real.volume_Icc, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc]
  rw [add_sub_cancel_left, ENNReal.toReal_inv, ENNReal.toReal_ofReal hQ.le, smul_eq_mul]

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    HasDerivAt (rqCDF R Q m s)
      (1 / Q * (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) ((R + Q - x - m) / s)
                 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) ((R - x - m) / s))) x := by
  set g : ℝ → ℝ := fun v => 1 - cdf (gaussianReal 0 1) ((v - m) / s) with hg
  have hgc : Continuous g :=
    continuous_const.sub (p4e4_cdf_cont.comp ((continuous_id.sub continuous_const).div_const _))
  set G : ℝ → ℝ := fun t => ∫ v in (0:ℝ)..t, g v with hG
  have hGd : ∀ t, HasDerivAt G (g t) t := fun t =>
    (hgc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hF : rqCDF R Q m s = fun y => Q⁻¹ * (G (R + Q - y) - G (R - y)) := by
    funext y
    rw [p4e4_integral R Q m s y hQ hs]
    congr 1
    have h1 : ∫ u in R..R + Q, (1 - cdf (gaussianReal 0 1) ((u - y - m) / s))
        = ∫ u in R..R + Q, g (u - y) := rfl
    rw [h1, intervalIntegral.integral_comp_sub_right g y]
    simp only [hG]
    rw [intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)]
  rw [hF]
  have hA : HasDerivAt (fun y => G (R + Q - y)) (g (R + Q - x) * (-1)) x :=
    (hGd (R + Q - x)).comp x ((hasDerivAt_id x).const_sub (R + Q))
  have hB : HasDerivAt (fun y => G (R - y)) (g (R - x) * (-1)) x :=
    (hGd (R - x)).comp x ((hasDerivAt_id x).const_sub R)
  refine ((hA.sub hB).const_mul Q⁻¹).congr_deriv ?_
  simp only [hg]
  ring
