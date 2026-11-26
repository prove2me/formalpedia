-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BoundedContinuousDCTV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:27:07.145912+00:00
-- url     : https://prove2.me/submissions/8e8c66cb-c57f-4f4e-91af-8da5a39d9d1d

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (M : Nat → Omega → Real) (Mlim : Omega → Real)
    (hM : ∀ n, Measurable (M n))
    (hlim : ∀ᵐ w ∂P, Tendsto (fun n => M n w) atTop (nhds (Mlim w)))
    (f : BoundedContinuousFunction Real Real) :
    Tendsto (fun n => ∫ w, f (M n w) ∂P) atTop
      (nhds (∫ w, f (Mlim w) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (hM n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall fun w => f.norm_coe_le_norm (M n w)
  · filter_upwards [hlim] with w hw
    exact (f.continuous.continuousAt.tendsto).comp hw
