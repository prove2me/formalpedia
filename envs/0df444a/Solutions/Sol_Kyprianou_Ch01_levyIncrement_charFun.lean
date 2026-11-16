-- Prove2me | solution 1 for Kyprianou.Ch01.levyIncrement_charFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:42:37.656545+00:00
-- url     : https://prove2.me/submissions/646a26e0-bcf6-4bbc-ad84-c013616c65df

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_LevyProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A stationary Lévy increment has the characteristic function of its duration. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (theta : ℝ) (Psi : ℂ)
    (hchar : ∀ t : ℝ≥0,
      charFun (P.map (X t)) theta =
        Complex.exp (-((t : ℝ) : ℂ) * Psi))
    (s t : ℝ≥0) (hst : s ≤ t) :
    charFun (P.map (fun ω => X t ω - X s ω)) theta =
      Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * Psi) := by
  have hdist := (hX.stationary_increments s (t - s)).map_eq
  have ht : s + (t - s) = t := add_tsub_cancel_of_le hst
  have hzero : increment X 0 (t - s) = X (t - s) := by
    funext ω
    simp [increment, hX.start_zero]
  rw [ht, hzero] at hdist
  change P.map (fun ω => X t ω - X s ω) =
    P.map (X (t - s)) at hdist
  rw [hdist]
  exact hchar (t - s)
