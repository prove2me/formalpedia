-- Prove2me | solution 1 for Kyprianou.Ch01.measurableReciprocalOccupationFromJointIntegerProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:11:57.968802+00:00
-- url     : https://prove2.me/submissions/f5091664-faef-447a-a545-edaae1481b45

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The nonnegative reciprocal occupation integral has measurable
fixed-time sections whenever its integer path is jointly measurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (t : ℝ≥0) :
    Measurable (fun ω : Ω => reciprocalOccupation X t ω) := by
  have hTime : Measurable (fun z : Ω × ℝ =>
      ((Real.toNNReal z.2 : ℝ≥0), z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hX : Measurable (fun z : Ω × ℝ =>
      X (Real.toNNReal z.2) z.1) := hJoint.comp hTime
  have hCast : Measurable (fun n : ℤ => (n : ℝ)) :=
    (continuous_of_discreteTopology : Continuous fun n : ℤ => (n : ℝ)).measurable
  have hE : Measurable (fun z : Ω × ℝ =>
      (ENNReal.ofReal (X (Real.toNNReal z.2) z.1 : ℝ))⁻¹) :=
    (ENNReal.measurable_ofReal.comp (hCast.comp hX)).inv
  have hIntegral : Measurable (fun ω : Ω =>
      ∫⁻ s : ℝ, (ENNReal.ofReal
        (X (Real.toNNReal s) ω : ℝ))⁻¹
          ∂(volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ)))) :=
    hE.lintegral_prod_right
  simpa only [reciprocalOccupation] using hIntegral
