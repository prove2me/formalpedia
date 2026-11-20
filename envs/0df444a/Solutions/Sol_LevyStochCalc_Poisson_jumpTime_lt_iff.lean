-- Prove2me | solution 1 for LevyStochCalc.Poisson.jumpTime_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T13:51:59.93658+00:00
-- url     : https://prove2.me/submissions/99de6d45-2a13-441d-bbc9-6f2847866487

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LevyStochCalc.Poisson

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν) (A : Set E) (i : ℕ) (t : ℝ) (ω : Ω) :
    jumpTime N A i ω < (t : WithTop ℝ)
      ↔ ∃ s : ℝ, 0 ≤ s ∧ s < t ∧ (i : ℝ≥0∞) ≤ arrivalCount N A s ω := by
  classical
  constructor
  · intro h
    unfold jumpTime at h
    split_ifs at h with hne
    · have h' : sInf (jumpTimeSet N A i ω) < t := WithTop.coe_lt_coe.mp h
      obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne h'
      exact ⟨s, hs.1, hst, hs.2⟩
    · exact absurd h (not_lt.mpr le_top)
  · rintro ⟨s, hs0, hst, hi⟩
    have hmem : s ∈ jumpTimeSet N A i ω := ⟨hs0, hi⟩
    unfold jumpTime
    rw [if_pos ⟨s, hmem⟩]
    exact WithTop.coe_lt_coe.mpr (lt_of_le_of_lt (csInf_le (bddBelow_jumpTimeSet N A i ω) hmem) hst)
