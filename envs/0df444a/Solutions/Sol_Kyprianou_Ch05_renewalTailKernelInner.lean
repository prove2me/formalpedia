-- Prove2me | solution 1 for Kyprianou.Ch05.renewalTailKernelInner
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:01:40.582285+00:00
-- url     : https://prove2.me/submissions/246086c5-4ce9-4358-b5a3-7cca132ba5ab

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The inner strict upper-ray kernel is the shifted strict tail. -/
theorem solution
    (F : Measure Real) (v x u y : Real) (hu : 0 < u) :
    (∫⁻ z in Ioi (x-v),
      (if z-(x-v) ∈ Ioi u ∧ x-v ∈ Ioi y then (1 : ENNReal) else 0) ∂F) =
      if y < x-v then F (Ioi (x-v+u)) else 0 := by
  by_cases h : y < x-v
  · rw [if_pos h]
    have he : (fun z : Real => if z-(x-v) ∈ Ioi u ∧ x-v ∈ Ioi y then (1 : ENNReal) else 0) =
        (Ioi (x-v+u)).indicator 1 := by
      funext z
      have hz : u < z-(x-v) ↔ x-v+u < z := by constructor <;> intro hh <;> linarith
      simp [Set.indicator,mem_Ioi,h,hz]
    rw [he,lintegral_indicator_one measurableSet_Ioi,Measure.restrict_apply measurableSet_Ioi]
    congr 1
    exact inter_eq_left.mpr (Ioi_subset_Ioi (by linarith))
  · simp [mem_Ioi,h]
