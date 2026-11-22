-- Prove2me | solution 1 for Kyprianou.Ch01.levyIncrement_McKeanIntegralStationary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:05:54.592854+00:00
-- url     : https://prove2.me/submissions/3e8b1d37-15b3-44f7-80ea-060e2d6b66b1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanValue_measurable
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Integrals of any measurable shifted McKean payoff respect Lévy stationarity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (s t : ℝ≥0) (hst : s ≤ t)
    (K b phi y : ℝ) :
    (∫ ω, mckeanValue K b phi (y + (X t ω - X s ω)) ∂P) =
      (∫ ω, mckeanValue K b phi (y + X (t - s) ω) ∂P) := by
  have hdist : IdentDistrib
      (fun ω => X t ω - X s ω) (X (t - s)) P P := by
    have hi := hX.stationary_increments s (t - s)
    have ht : s + (t - s) = t := add_tsub_cancel_of_le hst
    have hz : increment X 0 (t - s) = X (t - s) := by
      funext ω
      simp [increment, hX.start_zero]
    rw [ht, hz] at hi
    exact hi
  have hf : Measurable (fun z : ℝ => mckeanValue K b phi (y + z)) :=
    (Kyprianou.Ch01.mckeanValue_measurable K b phi).comp
      (measurable_const.add measurable_id)
  have heq := (hdist.comp hf).integral_eq
  simpa only [Function.comp_def] using heq
