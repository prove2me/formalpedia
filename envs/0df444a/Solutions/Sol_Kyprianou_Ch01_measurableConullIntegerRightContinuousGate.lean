-- Prove2me | solution 1 for Kyprianou.Ch01.measurableConullIntegerRightContinuousGate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:50:32.002748+00:00
-- url     : https://prove2.me/submissions/36069c5f-97fc-4ca1-a45a-e7a47e1bb0aa

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A measurable conull set carries all right-continuity conditions
simultaneously, even if the original event is not measurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ≥0 → Ω → ℤ)
    (hRight : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Set.Ici t) t) :
    ∃ G : Set Ω, MeasurableSet G ∧
      (∀ᵐ ω ∂P, ω ∈ G) ∧
      ∀ ω ∈ G, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Set.Ici t) t := by
  let B : Set Ω := {ω | ¬ ∀ t : ℝ≥0,
    ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Set.Ici t) t}
  have hBnull : P B = 0 := (ae_iff).mp hRight
  obtain ⟨N, hBN, hNmeas, hNzero⟩ :=
    exists_measurable_superset_of_null hBnull
  refine ⟨Nᶜ, hNmeas.compl, ?_, ?_⟩
  · apply (ae_iff).2
    simpa using hNzero
  · intro ω hω
    by_contra hbad
    exact hω (hBN hbad)
