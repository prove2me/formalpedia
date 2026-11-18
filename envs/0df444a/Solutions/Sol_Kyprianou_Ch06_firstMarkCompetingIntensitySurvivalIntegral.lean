-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkCompetingIntensitySurvivalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:52:50.137331+00:00
-- url     : https://prove2.me/submissions/10c45d33-7091-4df3-9807-6977c411e3f9

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_competingPoissonRateExponentialTailIntegral
import Theorems.Thm_Kyprianou_Ch06_firstMarkCompetingRegionIntensitySplit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E] (n : Measure E)
    (A C : Set E) (hC : MeasurableSet C)
    (hFinite : n A < ⊤) (hPositive : 0 < n (A ∩ C))
    (t : Real) :
    (∫ s in Set.Ioi t,
      (n (A ∩ C)).toReal *
        Real.exp (-((n A).toReal * s))) =
      ((n (A ∩ C)).toReal / (n A).toReal) *
        Real.exp (-((n A).toReal * t)) := by
  have hFinitePart : n (A ∩ C) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hFinite
  have ha : 0 < (n (A ∩ C)).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hPositive, hFinitePart⟩
  have hb : 0 ≤ (n (A \ C)).toReal :=
    ENNReal.toReal_nonneg
  have hRate :=
    (Kyprianou.Ch06.firstMarkCompetingRegionIntensitySplit
      n A C hC hFinite).2
  have hIntegral :=
    Kyprianou.Ch06.competingPoissonRateExponentialTailIntegral
      (n (A ∩ C)).toReal (n (A \ C)).toReal t ha hb
  simpa only [hRate, neg_mul] using hIntegral
