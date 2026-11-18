-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkENNRealCompetingRateTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:58:22.084575+00:00
-- url     : https://prove2.me/submissions/7230c61e-99e8-44d5-afca-4690942132e1

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstMarkCompetingIntensitySurvivalIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E] (n : Measure E)
    (A C : Set E) (hC : MeasurableSet C)
    (hFinite : n A < ⊤) (hPositive : 0 < n (A ∩ C))
    (t : Real) :
    ENNReal.ofReal
      (∫ s in Set.Ioi t,
        (n (A ∩ C)).toReal *
          Real.exp (-((n A).toReal * s))) =
      (n (A ∩ C) / n A) *
        ENNReal.ofReal (Real.exp (-((n A).toReal * t))) := by
  have hFinitePart : n (A ∩ C) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hFinite
  have hTotalPositive : 0 < n A :=
    lt_of_lt_of_le hPositive (measure_mono Set.inter_subset_left)
  have hRealTotal : 0 < (n A).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hTotalPositive, hFinite⟩
  have hRatioNonneg :
      0 ≤ (n (A ∩ C)).toReal / (n A).toReal :=
    div_nonneg ENNReal.toReal_nonneg (le_of_lt hRealTotal)
  have hConvert :
      ENNReal.ofReal ((n (A ∩ C)).toReal / (n A).toReal) =
        n (A ∩ C) / n A := by
    rw [ENNReal.ofReal_div_of_pos hRealTotal,
      ENNReal.ofReal_toReal (ne_of_lt hFinitePart),
      ENNReal.ofReal_toReal (ne_of_lt hFinite)]
  have hReal :=
    Kyprianou.Ch06.firstMarkCompetingIntensitySurvivalIntegral
      n A C hC hFinite hPositive t
  rw [hReal, ENNReal.ofReal_mul hRatioNonneg, hConvert]
