-- Prove2me | solution 1 for Kyprianou.Ch01.firstLowerPassageEqShiftedNegUpperPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:18:48.782343+00:00
-- url     : https://prove2.me/submissions/3585c91b-e0fe-4b79-9562-7a81b7ffdf1a

import Mathlib.Tactic.Linarith
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (x barrier : ℝ) :
    firstLowerPassage X x barrier =
      firstUpperPassage (fun t ω => -X t ω) (x - barrier) := by
  classical
  funext ω
  have hiff (t : ℝ≥0) :
      (0 < t ∧ x + X t ω < barrier) ↔
        (0 < t ∧ x - barrier < -X t ω) := by
    constructor
    · rintro ⟨ht, hcross⟩
      exact ⟨ht, by linarith⟩
    · rintro ⟨ht, hcross⟩
      exact ⟨ht, by linarith⟩
  have hex :
      (∃ t : ℝ≥0, 0 < t ∧ x + X t ω < barrier) ↔
        (∃ t : ℝ≥0, 0 < t ∧ x - barrier < -X t ω) :=
    exists_congr hiff
  have hset :
      {t : ℝ≥0 | 0 < t ∧ x + X t ω < barrier} =
        {t : ℝ≥0 | 0 < t ∧ x - barrier < -X t ω} :=
    Set.ext (fun t => hiff t)
  unfold firstLowerPassage firstUpperPassage
  simp only [hex, hset]
  by_cases h : ∃ t : ℝ≥0, 0 < t ∧ x - barrier < -X t ω
  · simp [h, hset]
    rfl
  · simp [h, hset]
