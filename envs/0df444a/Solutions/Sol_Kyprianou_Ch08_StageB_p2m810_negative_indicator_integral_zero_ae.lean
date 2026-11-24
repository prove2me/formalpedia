-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_negative_indicator_integral_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:38:03.384255+00:00
-- url     : https://prove2.me/submissions/fafa8de4-941f-45f2-9a57-c29316209d6f

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- A nonnegative bounded indicator vanishes almost surely. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Y : Ω → ℝ) (c : ℝ),
      AEMeasurable Y P →
      (∫ ω, if Y ω<c then (1:ℝ) else 0 ∂P) = 0 →
      ∀ᵐ ω ∂P, c ≤ Y ω := by
  intro Ω mΩ P hP Y c hm hI
  let f : ℝ → ℝ := fun z => if z<c then 1 else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
  have hfi : Integrable (fun ω => f (Y ω)) P :=
    (integrable_const (1:ℝ)).mono' (hf.comp_aemeasurable hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by dsimp [f]; split <;> norm_num)
  have hnon : 0 ≤ (fun ω => f (Y ω)) := by intro ω; dsimp [f]; split <;> norm_num
  filter_upwards [(integral_eq_zero_iff_of_nonneg hnon hfi).1 hI] with ω hw
  by_contra! h
  simp [f,h] at hw
