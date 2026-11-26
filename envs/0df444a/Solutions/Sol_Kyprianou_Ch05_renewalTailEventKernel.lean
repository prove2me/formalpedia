-- Prove2me | solution 1 for Kyprianou.Ch05.renewalTailEventKernel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:59:32.0768+00:00
-- url     : https://prove2.me/submissions/8f43fe95-6d9b-4b98-8e5b-f9440ac0fcaa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Theorems.Thm_Kyprianou_Ch05_renewalTailJointKernelENN
import Theorems.Thm_Kyprianou_Ch05_renewalJointKernelTailReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Convert the positive passage kernel to the real tail convolution. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x u y : Real) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    (P {w : Omega | u < renewalOvershoot Z x w ∧ y < renewalUndershoot Z x w}).toReal =
    ∫ z in Icc (0 : Real) x,
      (if y < x-z then (F (Ioi (x-z+u))).toReal else 0) ∂(renewalMeasure F) := by
  haveI : IsProbabilityMeasure F := ⟨by
    rw [← hRenewal.2.1 0, Measure.map_apply (hRenewal.1 0) MeasurableSet.univ]
    simp⟩
  rw [renewalTailJointKernelENN P Z F hRenewal x u y hx hu]
  exact renewalJointKernelTailReal (renewalMeasure F) F x u y hu
