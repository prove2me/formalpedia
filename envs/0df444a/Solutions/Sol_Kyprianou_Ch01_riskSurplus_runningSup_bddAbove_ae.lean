-- Prove2me | solution 1 for Kyprianou.Ch01.riskSurplus_runningSup_bddAbove_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:07:14.050921+00:00
-- url     : https://prove2.me/submissions/8f806334-ff6c-456d-a542-061dec1c6610

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_isCadlag_ae
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (F : Measure ℝ)
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hr : 0 < rate) (premium x : ℝ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      BddAbove {z : ℝ | ∃ s : ℝ≥0,
        s ≤ T ∧ z = riskSurplus arrival claims premium x s ω} := by
  filter_upwards [riskSurplus_isCadlag_ae P arrival claims rate F hd hr premium x]
    with ω hω
  intro T
  exact cadlag_runningSup_bddAbove _ hω T
