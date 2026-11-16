-- Prove2me | solution 1 for Kyprianou.Ch01.levyRealExpIncrementStationaryMean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T14:58:24.892212+00:00
-- url     : https://prove2.me/submissions/adcd8662-4ede-4080-b9e3-074d101eb4cd

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Pushforward law of a Lévy increment equals that at its duration. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, Real.exp (theta * (X t ω - X s ω)) ∂P) =
      (∫ ω, Real.exp (theta * X (t - s) ω) ∂P) := by
  have hdist := (hX.stationary_increments s (t - s)).map_eq
  have ht : s + (t - s) = t := add_tsub_cancel_of_le hst
  have hz : increment X 0 (t - s) = X (t - s) := by
    funext ω
    simp [increment, hX.start_zero]
  rw [ht, hz] at hdist
  change P.map (fun ω => X t ω - X s ω) =
    P.map (X (t - s)) at hdist
  have hG : Measurable (fun ω => X t ω - X s ω) :=
    (hMeas t).sub (hMeas s)
  have hphi : Measurable (fun z : ℝ => Real.exp (theta * z)) := by
    fun_prop
  calc
    (∫ ω, Real.exp (theta * (X t ω - X s ω)) ∂P) =
      (∫ z, Real.exp (theta * z) ∂P.map
        (fun ω => X t ω - X s ω)) := by
        rw [integral_map hG.aemeasurable hphi.aestronglyMeasurable]
    _ = (∫ z, Real.exp (theta * z) ∂P.map (X (t - s))) := by
      rw [hdist]
    _ = _ := by
      rw [integral_map (hMeas (t - s)).aemeasurable
        hphi.aestronglyMeasurable]
