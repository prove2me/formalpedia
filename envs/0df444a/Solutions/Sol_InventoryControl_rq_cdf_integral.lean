-- Prove2me | solution 1 for InventoryControl.rq_cdf_integral
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T19:28:01.039458+00:00
-- url     : https://prove2.me/submissions/471ea625-28ac-434b-81b1-d1c19e1d4cfd

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory in
private lemma p78a_cdf_affine (m s x : ℝ) (hs : 0 < s) :
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
private lemma p78a_Ici (m s y : ℝ) (hs : 0 < s) :
    (newsboyDemand m s).real (Set.Ici y) = 1 - cdf (gaussianReal 0 1) ((y - m) / s) := by
  have hv : Real.toNNReal (s ^ 2) ≠ 0 := by simp [hs.ne']
  have := nullSingletonClass_gaussianReal (μ := m) (v := Real.toNNReal (s ^ 2)) hv
  rw [newsboyDemand_eq, ← p78a_cdf_affine m s y hs, cdf_eq_real]
  rw [measureReal_congr (Ioi_ae_eq_Ici (μ := gaussianReal m (Real.toNNReal (s ^ 2)))).symm]
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

open MeasureTheory ProbabilityTheory InventoryControl in
private lemma p78a_integral (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
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
    rw [h3, integral_indicator_one measurableSet_Ici, p78a_Ici m s _ hs]
  simp_rw [h2]
  unfold rqPosition ProbabilityTheory.cond
  rw [integral_smul_measure, Real.volume_Icc, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc]
  rw [add_sub_cancel_left, ENNReal.toReal_inv, ENNReal.toReal_ofReal hQ.le, smul_eq_mul]

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    rqCDF R Q m s x
      = (1 / Q) * ∫ u in R..R + Q,
          (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) ((u - x - m) / s)) := by
  rw [one_div]
  exact p78a_integral R Q m s x hQ hs
