-- Prove2me | solution 1 for Kyprianou.Ch05.renewalJointFiniteLevelSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:58:29.774793+00:00
-- url     : https://prove2.me/submissions/9debec20-6bac-4def-acce-7b70ecbfecba

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Theorems.Thm_Kyprianou_Ch05_renewalCrossingCountableMeasure
import Theorems.Thm_Kyprianou_Ch05_renewalCrossingCellMeasure
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

open Classical in
/-- Sum the crossing-cell probabilities using their epoch-spacing product laws. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x : Real) (hx : 0 < x)
    (A B : Set Real) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA2 : A ⊆ Ioi (0 : Real)) (hB2 : B ⊆ Ioc (0 : Real) x) :
    P {w : Omega | 0 < renewalOvershoot Z x w ∧
      renewalOvershoot Z x w ∈ A ∧ renewalUndershoot Z x w ∈ B} =
    ∑' n : Nat, ∫⁻ v in Icc (0 : Real) x,
      (∫⁻ z in Ioi (x-v),
        (if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0) ∂F)
      ∂(renewalConvolutionPower F n) := by
  rw [renewalCrossingCountableMeasure P Z F hRenewal x hx A B hA hB hA2]
  congr 1
  funext n
  exact renewalCrossingCellMeasure P Z F hRenewal x A B hA hB hA2 n
