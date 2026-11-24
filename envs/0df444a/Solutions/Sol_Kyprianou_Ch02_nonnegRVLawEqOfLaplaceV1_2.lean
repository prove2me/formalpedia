-- Prove2me | solution 2 for Kyprianou.Ch02.nonnegRVLawEqOfLaplaceV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T05:22:41.470065+00:00
-- url     : https://prove2.me/submissions/1bb90209-37a1-4b50-9559-e52f01c33f0d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Exponential moments on the positive ray of the law of `-C`, for `C ≥ 0`, are finite. -/
lemma neg_law_integrable_exp {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (C : Ω → ℝ) (hmC : Measurable C) (hnC : ∀ ω, 0 ≤ C ω)
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ => Real.exp (s * x)) (μ.map (fun ω => -C ω)) := by
  have hmC' : Measurable (fun ω => -C ω) := hmC.neg
  have hcont : Continuous (fun x : ℝ => Real.exp (s * x)) := by fun_prop
  rw [integrable_map_measure hcont.aestronglyMeasurable hmC'.aemeasurable]
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (hcont.measurable.comp hmC').aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs, Real.abs_exp]
    rw [Real.exp_le_one_iff]
    have := hnC ω
    nlinarith

/-- Change of variables for the exponential moment of the law of `-C`. -/
lemma neg_law_integral_exp {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (C : Ω → ℝ) (hmC : Measurable C) (s : ℝ) :
    MeasureTheory.integral (μ.map (fun ω => -C ω)) (fun x : ℝ => Real.exp (s * x)) =
      MeasureTheory.integral μ (fun ω => Real.exp (-(s * C ω))) := by
  have hcont : Continuous (fun x : ℝ => Real.exp (s * x)) := by fun_prop
  have hmC' : Measurable (fun ω => -C ω) := hmC.neg
  rw [integral_map hmC'.aemeasurable hcont.aestronglyMeasurable]
  congr 1
  funext ω
  ring_nf

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A B : Ω → ℝ) (hmA : Measurable A) (hmB : Measurable B)
    (hnA : ∀ ω, 0 ≤ A ω) (hnB : ∀ ω, 0 ≤ B ω)
    (h : ∀ s : ℝ, 0 < s →
      (∫ ω, Real.exp (-(s*A ω)) ∂P) = ∫ ω, Real.exp (-(s*B ω)) ∂Q) :
    P.map A = Q.map B := by
  have hmA' : Measurable (fun ω => -A ω) := hmA.neg
  have hmB' : Measurable (fun ω => -B ω) := hmB.neg
  have : IsProbabilityMeasure (P.map (fun ω => -A ω)) :=
    Measure.isProbabilityMeasure_map hmA'.aemeasurable
  have : IsProbabilityMeasure (Q.map (fun ω => -B ω)) :=
    Measure.isProbabilityMeasure_map hmB'.aemeasurable
  have key : P.map (fun ω => -A ω) = Q.map (fun ω => -B ω) := by
    refine AvramDividend.Classical.measure_eq_of_pos_mgf_on_ray
      (neg_law_integrable_exp P A hmA hnA) (neg_law_integrable_exp Q B hmB hnB) ?_
    intro s hs
    rw [neg_law_integral_exp P A hmA s, neg_law_integral_exp Q B hmB s]
    exact h s hs
  -- negate again
  have hA : P.map A = (P.map (fun ω => -A ω)).map (fun x : ℝ => -x) := by
    rw [Measure.map_map measurable_neg hmA']
    congr 1
    funext ω
    simp
  have hB : Q.map B = (Q.map (fun ω => -B ω)).map (fun x : ℝ => -x) := by
    rw [Measure.map_map measurable_neg hmB']
    congr 1
    funext ω
    simp
  rw [hA, hB, key]
