-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassageNaturalStoppingContinuous
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-11-16T09:02:04.247142+00:00
-- url     : https://prove2.me/submissions/105bd2a0-01a7-41c1-abb1-c705eeecef2c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01
open scoped NNReal Topology
set_option autoImplicit false

private def counterexampleX (t : ℝ≥0) (b : Bool) : ℝ :=
  if b then (t : ℝ) else min (t : ℝ) 1

private theorem counterexampleContinuous (ω : Bool) :
    Continuous (fun t : ℝ≥0 => counterexampleX t ω) := by
  cases ω <;> simp [counterexampleX] <;> fun_prop

private theorem counterexampleSigmaBot :
    naturalSigma counterexampleX (1 : ℝ≥0) = ⊥ := by
  have hconst (t : ℝ≥0) (ht : t ≤ 1) :
      counterexampleX t = fun _ : Bool => (t : ℝ) := by
    funext b
    cases b
    · simp only [counterexampleX, Bool.false_eq_true, ↓reduceIte]
      exact min_eq_left (by exact_mod_cast ht)
    · simp [counterexampleX]
  unfold naturalSigma PerfCorrMSQ.natFiltr
  refine le_antisymm ?_ bot_le
  refine iSup_le fun t => iSup_le fun ht => ?_
  rw [hconst t ht]
  simp [MeasurableSpace.comap_const]

private theorem counterexamplePassages :
    firstUpperPassage counterexampleX 1 false = ⊤ ∧
    firstUpperPassage counterexampleX 1 true =
      (1 : WithTop ℝ≥0) := by
  constructor
  · have hn : ¬ ∃ t : ℝ≥0, 0 < t ∧ 1 < counterexampleX t false := by
      rintro ⟨t, _, ht⟩
      have hx : counterexampleX t false ≤ 1 := by
        simp [counterexampleX]
      exact (not_lt_of_ge hx) ht
    simp [firstUpperPassage, hn]
  · have hp : ∃ t : ℝ≥0, 0 < t ∧ 1 < counterexampleX t true := by
      refine ⟨2, by norm_num, ?_⟩
      norm_num [counterexampleX]
    have hs : ({t : ℝ≥0 |
        0 < t ∧ 1 < counterexampleX t true} : Set ℝ≥0) =
        Set.Ioi (1 : ℝ≥0) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Ioi]
      constructor
      · rintro ⟨_, ht⟩
        simpa [counterexampleX] using ht
      · intro ht
        exact ⟨lt_trans (by norm_num) ht,
          by simpa [counterexampleX] using ht⟩
    simp [firstUpperPassage, hp, hs, csInf_Ioi]

theorem solution :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
      (X : ℝ≥0 → Ω → ℝ),
      (∀ t : ℝ≥0, Measurable (X t)) →
      (∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) →
      ∀ (s : ℝ), 0 < s →
        Kyprianou.Ch01.IsNaturalStoppingTime X
          (Kyprianou.Ch01.firstUpperPassage X s)) := by
  intro h
  letI : MeasurableSpace Bool := ⊤
  have hm : @MeasurableSet Bool (naturalSigma counterexampleX 1)
      {ω | firstUpperPassage counterexampleX 1 ω ≤ (1 : WithTop ℝ≥0)} :=
    (h (Ω := Bool) counterexampleX
      (fun t => Measurable.of_discrete)
      counterexampleContinuous 1 (by norm_num)) 1
  have hbot : @MeasurableSet Bool ⊥ ({true} : Set Bool) := by
    have hS : ({ω : Bool |
        firstUpperPassage counterexampleX 1 ω ≤
          (1 : WithTop ℝ≥0)} : Set Bool) = {true} := by
      ext ω
      rcases counterexamplePassages with ⟨hfalse, htrue⟩
      cases ω <;> simp [hfalse, htrue]
    rw [hS] at hm
    rw [counterexampleSigmaBot] at hm
    exact hm
  rcases MeasurableSpace.measurableSet_bot_iff.mp hbot with he | he
  · have ht : true ∈ ({true} : Set Bool) := by simp
    rw [he] at ht
    simpa using ht
  · have hf : false ∈ ({true} : Set Bool) := by rw [he]; trivial
    simpa using hf
