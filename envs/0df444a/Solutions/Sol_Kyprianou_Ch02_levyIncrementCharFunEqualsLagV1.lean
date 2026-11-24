-- Prove2me | solution 1 for Kyprianou.Ch02.levyIncrementCharFunEqualsLagV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:05:03.925197+00:00
-- url     : https://prove2.me/submissions/c9bfc270-99ed-4630-9239-750e2e4a9ead

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) (s t : ℝ≥0) (hst : s ≤ t) (ξ : ℝ) :
    charFun (P.map (increment X s t)) ξ = charFun (P.map (X (t-s))) ξ := by
  have h := hX.stationary_increments s (t-s)
  rw [add_tsub_cancel_of_le hst] at h
  have he : increment X 0 (t-s) = X (t-s) := by
    funext ω
    simp [increment, hX.start_zero]
  rw [he] at h
  rw [h.map_eq]
