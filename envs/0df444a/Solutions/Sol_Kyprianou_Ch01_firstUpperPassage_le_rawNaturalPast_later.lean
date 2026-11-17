-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassage_le_rawNaturalPast_later
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T19:03:20.863207+00:00
-- url     : https://prove2.me/submissions/3b700d30-58c9-40d3-ac58-69798ada0295

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_rationalApproxEvent
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageRationalCrossingMeasurable
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (t v : ℝ≥0) (htv : t < v) :
    @MeasurableSet Ω (naturalSigma X v)
      {ω | firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0)} := by
  classical
  have htvle : t ≤ v := le_of_lt htv
  have hhorizon (n : ℕ) :
      t + (v - t) / ((n : ℝ≥0) + 2) ≤ v := by
    calc
      t + (v - t) / ((n : ℝ≥0) + 2) ≤ t + (v - t) := by
        gcongr
        exact div_le_self (by positivity)
          (by nlinarith [show (0 : ℝ≥0) ≤ (n : ℝ≥0) from bot_le])
      _ = v := add_tsub_cancel_of_le htvle
  rw [firstUpperPassage_rationalApproxEvent X hContinuous s t v htv]
  apply MeasurableSet.iInter
  intro n
  have hraw := firstUpperPassageRationalCrossingMeasurable X
    (t + (v - t) / ((n : ℝ≥0) + 2)) s
  exact (naturalSigma_monotone X (hhorizon n)) _ hraw
