-- Prove2me | solution 1 for Kyprianou.Ch01.continuousRepresentativeForAlmostSurePaths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:22:53.428317+00:00
-- url     : https://prove2.me/submissions/6ae73246-03fa-4852-b034-4060ded78545

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContSet : MeasurableSet {ω | Continuous (fun t : ℝ≥0 => X t ω)})
    (hAE : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, Continuous (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = X t ω) := by
  classical
  refine ⟨fun t ω => if Continuous (fun s : ℝ≥0 => X s ω) then X t ω else 0, ?_, ?_, ?_⟩
  · intro ω
    by_cases h : Continuous (fun s : ℝ≥0 => X s ω)
    · simpa only [if_pos h] using h
    · simpa only [if_neg h] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))
  · intro t
    exact Measurable.ite hContSet (hMeas t) measurable_const
  · filter_upwards [hAE] with ω hω
    intro t
    simp only [if_pos hω]
