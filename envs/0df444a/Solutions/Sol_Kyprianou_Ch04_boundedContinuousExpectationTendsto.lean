-- Prove2me | solution 1 for Kyprianou.Ch04.boundedContinuousExpectationTendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:23:30.963439+00:00
-- url     : https://prove2.me/submissions/dbcd9a77-2c66-4db0-ae57-51bf9cbb4c6f

import Mathlib
open MeasureTheory Filter
open scoped NNReal Topology
set_option autoImplicit false

/-- Bounded continuous expectations converge under almost-sure path convergence. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (Z : Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hlim : ∀ᵐ z ∂P, Tendsto (fun t => X t z) atTop (nhds (Z z)))
    (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun t => ∫ z, f (X t z) ∂P) atTop (nhds (∫ z, f (Z z) ∂P)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖)
  · exact Eventually.of_forall fun t => (f.continuous.measurable.comp (hm t)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => Eventually.of_forall fun z =>
      f.norm_coe_le_norm (X t z)
  · exact integrable_const _
  · filter_upwards [hlim] with z hz
    exact f.continuous.continuousAt.tendsto.comp hz
