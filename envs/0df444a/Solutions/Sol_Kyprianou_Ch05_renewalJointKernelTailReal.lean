-- Prove2me | solution 1 for Kyprianou.Ch05.renewalJointKernelTailReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:22:12.700932+00:00
-- url     : https://prove2.me/submissions/e07ebb6e-8e61-4368-b33b-10cddf5a3cea

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Theorems.Thm_Kyprianou_Ch05_renewalJointKernelTailENN
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Evaluate the joint kernel on strict upper rays. -/
theorem solution (V F : Measure Real) [IsFiniteMeasure F]
    (x u y : Real) (hu : 0 < u) :
    (renewalJointKernel V F x (Ioi u) (Ioi y)).toReal =
      ∫ v in Icc (0 : Real) x,
        (if y < x-v then (F (Ioi (x-v+u))).toReal else 0) ∂V := by
  classical
  let g : Real → Real := fun t => (F (Ioi t)).toReal
  have ha : Antitone g := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top F _) (measure_mono (Ioi_subset_Ioi hab))
  have hm : Measurable (fun v : Real => if y < x-v then g (x-v+u) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const (measurable_const.sub measurable_id))
      (ha.measurable.comp ((measurable_const.sub measurable_id).add_const u)) measurable_const
  rw [renewalJointKernelTailENN V F x u y hu]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun v => by
    split <;> positivity)) hm.aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro v
  by_cases hv : y < x-v
  · simp [hv, g, ENNReal.ofReal_toReal (measure_ne_top F _)]
  · simp [hv]
