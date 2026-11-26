-- Prove2me | solution 1 for Kyprianou.Ch05.renewalEpochMonotoneAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:00:56.646608+00:00
-- url     : https://prove2.me/submissions/0c4a7cc1-15b8-4549-9a70-81c2ee3bc518

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Kyprianou.Ch05
open Classical in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : ℕ → Omega → ℝ) (F : Measure ℝ)
    (hRenewal : IsRenewalEpochProcess P Z F) :
    ∀ᵐ w ∂P, Monotone (fun n => renewalEpoch Z n w) := by
  have hZ : ∀ᵐ w ∂P, ∀ n : ℕ, 0 ≤ Z n w := by
    rw [ae_all_iff]
    intro n
    rw [ae_iff]
    have h := congrArg (fun M : Measure ℝ => M (Iio 0)) (hRenewal.2.1 n)
    rw [Measure.map_apply (hRenewal.1 n) measurableSet_Iio] at h
    simp only [not_le]
    exact h.trans hRenewal.2.2.1
  filter_upwards [hZ] with w hw
  apply monotone_nat_of_le_succ
  intro n
  simp only [renewalEpoch,Finset.sum_range_succ]
  exact le_add_of_nonneg_right (hw n)
