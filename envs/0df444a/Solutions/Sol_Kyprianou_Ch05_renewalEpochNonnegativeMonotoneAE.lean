-- Prove2me | solution 1 for Kyprianou.Ch05.renewalEpochNonnegativeMonotoneAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:59:36.987347+00:00
-- url     : https://prove2.me/submissions/ebb93465-af9d-42f5-9fc2-e0f8382b37dd

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Nonnegative renewal spacings give almost surely nonnegative monotone epochs. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F) :
    ∀ᵐ w ∂P, (∀ n : Nat, 0 ≤ Z n w) ∧
      Monotone (fun n : Nat => renewalEpoch Z n w) := by
  have hz (n : Nat) : ∀ᵐ w ∂P, 0 ≤ Z n w := by
    rw [ae_iff]
    have he := congrArg (fun m : Measure Real => m (Iio 0)) (hRenewal.2.1 n)
    rw [Measure.map_apply (hRenewal.1 n) measurableSet_Iio] at he
    simpa only [not_le, Set.preimage, mem_Iio] using he.trans hRenewal.2.2.1
  filter_upwards [ae_all_iff.mpr hz] with w hw
  refine ⟨hw, monotone_nat_of_le_succ ?_⟩
  intro n
  rw [renewalEpoch, renewalEpoch, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (hw n)
