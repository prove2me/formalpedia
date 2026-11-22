-- Prove2me | solution 1 for Kyprianou.Ch01.measurableRealOccupationIntervalIntegralOfJoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:00:44.059704+00:00
-- url     : https://prove2.me/submissions/1eb09968-4be3-482b-98f2-4a7939c0f739

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An occupation clock integrated over a deterministic finite interval has
measurable sample sections when the process is jointly measurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℝ≥0 → Ω → ℝ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => Z z.1 z.2))
    (t : ℝ≥0) :
    Measurable (fun ω : Ω =>
      ∫ s in (0 : ℝ)..(t : ℝ), Z (Real.toNNReal s) ω) := by
  have hTime : Measurable (fun z : Ω × ℝ =>
      ((Real.toNNReal z.2 : ℝ≥0), z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk
      measurable_fst
  have hComp : Measurable (fun z : Ω × ℝ =>
      Z (Real.toNNReal z.2) z.1) := hJoint.comp hTime
  have hInt : StronglyMeasurable (fun ω : Ω =>
      ∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
        Z (Real.toNNReal s) ω ∂volume) :=
    hComp.stronglyMeasurable.integral_prod_right
  have hEq : (fun ω : Ω =>
      ∫ s in (0 : ℝ)..(t : ℝ),
        Z (Real.toNNReal s) ω) =
      (fun ω : Ω =>
        ∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
          Z (Real.toNNReal s) ω ∂volume) := by
    funext ω
    exact intervalIntegral.integral_of_le (NNReal.coe_nonneg t)
  exact hEq ▸ hInt.measurable
