-- Prove2me | solution 1 for Kyprianou.Ch05.renewalCrossingCellMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:03:33.679062+00:00
-- url     : https://prove2.me/submissions/25a02e62-350c-4976-9557-fbf79029463b

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_renewalEpochPairLawV1
import Theorems.Thm_Kyprianou_Ch05_renewalCrossingProductKernelV1
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

open Classical in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x : Real) (A B : Set Real) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA2 : A ⊆ Ioi 0) (n : Nat) :
    P ((fun n : Nat => {w : Omega |
      renewalEpoch Z n w ∈ Icc 0 x ∧
      Z n w - (x-renewalEpoch Z n w) ∈ A ∧
      x-renewalEpoch Z n w ∈ B}) n) =
    ∫⁻ v in Icc (0 : Real) x,
      (∫⁻ z in Ioi (x-v),
        (if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0) ∂F)
      ∂(renewalConvolutionPower F n) := by
  let C : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (0 : ℝ) x ∧
    p.2-(x-p.1) ∈ A ∧ x-p.1 ∈ B}
  have hC : MeasurableSet C :=
    (measurable_fst measurableSet_Icc).inter
      (((measurable_snd.sub (measurable_const.sub measurable_fst)) hA).inter
        ((measurable_const.sub measurable_fst) hB))
  have hm : Measurable (renewalEpoch Z n) := by
    unfold renewalEpoch
    exact Finset.measurable_sum _ fun j _ => hRenewal.1 j
  letI : IsProbabilityMeasure F := by
    rw [← hRenewal.2.1 n]
    exact Measure.isProbabilityMeasure_map (hRenewal.1 n).aemeasurable
  change P ((fun w => (renewalEpoch Z n w,Z n w)) ⁻¹' C) = _
  rw [← Measure.map_apply (hm.prodMk (hRenewal.1 n)) hC,
    renewalEpochPairLawV1 P Z F hRenewal n]
  exact renewalCrossingProductKernelV1 (renewalConvolutionPower F n) F x A B hA hB hA2
