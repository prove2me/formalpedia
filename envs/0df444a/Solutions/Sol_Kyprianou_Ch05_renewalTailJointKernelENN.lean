-- Prove2me | solution 1 for Kyprianou.Ch05.renewalTailJointKernelENN
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:59:31.034796+00:00
-- url     : https://prove2.me/submissions/35fd7b75-eb95-48f7-bdb4-f79be4c695d3

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Theorems.Thm_Kyprianou_Ch05_renewalCrossingCountableMeasure
import Theorems.Thm_Kyprianou_Ch05_renewalCrossingCellMeasure
import Theorems.Thm_Kyprianou_Ch05_renewalKernelSumInterchange
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Positive overshoot and undershoot tails equal the joint renewal kernel. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x u y : Real) (hx : 0 < x) (hu : 0 < u) :
    P {w : Omega | u < renewalOvershoot Z x w ∧ y < renewalUndershoot Z x w} =
      renewalJointKernel (renewalMeasure F) F x (Ioi u) (Ioi y) := by
  classical
  have he : {w : Omega | u < renewalOvershoot Z x w ∧ y < renewalUndershoot Z x w} =
      {w : Omega | 0 < renewalOvershoot Z x w ∧
        renewalOvershoot Z x w ∈ Ioi u ∧ renewalUndershoot Z x w ∈ Ioi y} := by
    ext w
    simp only [mem_setOf_eq,mem_Ioi]
    exact ⟨fun h => ⟨hu.trans h.1,h⟩,fun h => h.2⟩
  rw [he,renewalCrossingCountableMeasure P Z F hRenewal x hx _ _
    measurableSet_Ioi measurableSet_Ioi (Ioi_subset_Ioi hu.le)]
  rw [← renewalKernelSumInterchange F x (Ioi u) (Ioi y)]
  congr 1
  funext n
  exact renewalCrossingCellMeasure P Z F hRenewal x _ _
    measurableSet_Ioi measurableSet_Ioi (Ioi_subset_Ioi hu.le) n
