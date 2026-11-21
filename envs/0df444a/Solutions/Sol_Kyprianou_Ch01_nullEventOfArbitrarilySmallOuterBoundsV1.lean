-- Prove2me | solution 1 for Kyprianou.Ch01.nullEventOfArbitrarilySmallOuterBoundsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:15:37.461687+00:00
-- url     : https://prove2.me/submissions/ff904a01-149a-4697-b56c-dad27d2a494e

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Set Ω) (A : ι → Set Ω)
    (hSub : ∀ i : ι, E ⊆ A i)
    (hSmall : ∀ δ : ℝ, 0 < δ →
      ∃ i : ι, (P (A i)).toReal < δ) :
    P E = 0 := by
  have hZero : (P E).toReal = 0 := by
    by_contra hn
    have hNonneg : 0 ≤ (P E).toReal := ENNReal.toReal_nonneg
    have hPos : 0 < (P E).toReal :=
      lt_of_le_of_ne hNonneg (Ne.symm hn)
    obtain ⟨i, hi⟩ := hSmall (P E).toReal hPos
    have hLe : (P E).toReal ≤ (P (A i)).toReal :=
      ENNReal.toReal_mono (measure_ne_top P (A i))
        (measure_mono (hSub i))
    exact (not_lt_of_ge hLe) hi
  calc
    P E = ENNReal.ofReal (P E).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top P E)).symm
    _ = 0 := by simp [hZero]
