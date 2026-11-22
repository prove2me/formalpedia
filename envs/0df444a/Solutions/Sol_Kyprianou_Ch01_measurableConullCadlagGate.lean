-- Prove2me | solution 1 for Kyprianou.Ch01.measurableConullCadlagGate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:54:05.631525+00:00
-- url     : https://prove2.me/submissions/542df085-fc57-4975-9b8e-1a40361e8227

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every a.e. càdlàg family admits a measurable conull event on which
all of its paths satisfy the càdlàg condition pointwise. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℝ≥0 → Ω → ℕ)
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∃ G : Set Ω, MeasurableSet G ∧
      (∀ᵐ ω ∂P, ω ∈ G) ∧
      ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => Y t ω) := by
  let B : Set Ω := {ω | ¬IsCadlag (fun t : ℝ≥0 => Y t ω)}
  have hBnull : P B = 0 := (ae_iff).mp hCadlag
  obtain ⟨N, hBN, hNmeas, hNzero⟩ :=
    exists_measurable_superset_of_null hBnull
  refine ⟨Nᶜ, hNmeas.compl, ?_, ?_⟩
  · apply (ae_iff).2
    simpa using hNzero
  · intro ω hω
    by_contra hbad
    exact hω (hBN hbad)
