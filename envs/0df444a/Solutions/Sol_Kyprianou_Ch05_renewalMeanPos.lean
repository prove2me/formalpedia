-- Prove2me | solution 1 for Kyprianou.Ch05.renewalMeanPos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:54:33.328566+00:00
-- url     : https://prove2.me/submissions/e2f0bcfc-8a3c-472f-a263-a571f6d0a39a

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- A nondegenerate nonnegative renewal spacing has positive finite mean. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (hInt : Integrable (fun z : Real => z) F) :
    0 < ∫ z : Real, z ∂F := by
  have hprob : IsProbabilityMeasure F := ⟨by
    rw [← hRenewal.2.1 0, Measure.map_apply (hRenewal.1 0) MeasurableSet.univ]
    simp⟩
  letI := hprob
  have hnn : ∀ᵐ z ∂F, 0 ≤ z := by
    rw [ae_iff]
    have hs : {z : Real | ¬ 0 ≤ z} = Set.Iio (0 : Real) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
    rw [hs]
    exact hRenewal.2.2.1
  by_contra! h
  have hz : (∫ z : Real, z ∂F) = 0 :=
    le_antisymm h (integral_nonneg_of_ae hnn)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hInt).mp hz
  change (∀ᵐ z ∂F, z = 0) at hae
  rw [ae_iff] at hae
  have hc : F ({0}ᶜ : Set Real) = 0 := hae
  have ht := measure_add_measure_compl (μ := F) (measurableSet_singleton (0 : Real))
  rw [hc, add_zero, measure_univ] at ht
  exact hRenewal.2.2.2.1 ht
