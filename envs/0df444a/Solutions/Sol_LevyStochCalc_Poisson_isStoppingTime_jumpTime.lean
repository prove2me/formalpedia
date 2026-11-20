-- Prove2me | solution 1 for LevyStochCalc.Poisson.isStoppingTime_jumpTime
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:22:21.330279+00:00
-- url     : https://prove2.me/submissions/f5fece3d-b840-44cc-b94e-b107a6ac2dbc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F000
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LevyStochCalc.Poisson

lemma jumpTime_le_iff' {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν) (A : Set E) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), arrivalCount N A t ω ≠ ⊤) (i : ℕ) (t : ℝ) (ω : Ω) :
    jumpTime N A i ω ≤ (t : WithTop ℝ) ↔ 0 ≤ t ∧ (i : ℝ≥0∞) ≤ arrivalCount N A t ω := by
  classical
  constructor
  · intro h
    unfold jumpTime at h
    split_ifs at h with hne
    · have h' : sInf (jumpTimeSet N A i ω) ≤ t := WithTop.coe_le_coe.mp h
      set s0 := sInf (jumpTimeSet N A i ω) with hs0
      have hs0nn : 0 ≤ s0 := le_csInf hne (fun x hx => hx.1)
      refine ⟨hs0nn.trans h', ?_⟩
      have hright := iInf_arrivalCount_gt N A hA (lt_add_one s0) (hfin ω (s0 + 1))
      have hi : (i : ℝ≥0∞) ≤ arrivalCount N A s0 ω := by
        rw [← hright]
        refine le_iInf₂ (fun s hs => ?_)
        obtain ⟨s', hs', hs's⟩ := exists_lt_of_csInf_lt hne hs
        exact hs'.2.trans (arrivalCount_mono N A ω hs's.le)
      exact hi.trans (arrivalCount_mono N A ω h')
    · exact absurd h (by simp)
  · rintro ⟨ht, hi⟩
    have hmem : t ∈ jumpTimeSet N A i ω := ⟨ht, hi⟩
    unfold jumpTime
    rw [if_pos ⟨t, hmem⟩]
    exact WithTop.coe_le_coe.mpr (csInf_le (bddBelow_jumpTimeSet N A i ω) hmem)

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν) (A : Set E) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), arrivalCount N A t ω ≠ ⊤) (i : ℕ) :
    IsStoppingTime ℱ (jumpTime N A i) := by
  intro t
  have hset : {ω | jumpTime N A i ω ≤ (t : WithTop ℝ)}
      = {ω | 0 ≤ t ∧ (i : ℝ≥0∞) ≤ arrivalCount N A t ω} := by
    ext ω; exact jumpTime_le_iff' N A hA hfin i t ω
  rw [hset]
  by_cases ht : 0 ≤ t
  · simp only [ht, true_and]
    exact measurableSet_le measurable_const (measurable_arrivalCount N A hℱ hA t)
  · simp [ht]
