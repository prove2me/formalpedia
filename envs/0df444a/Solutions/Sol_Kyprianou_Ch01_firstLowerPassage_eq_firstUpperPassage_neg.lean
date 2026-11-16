-- Prove2me | solution 1 for Kyprianou.Ch01.firstLowerPassage_eq_firstUpperPassage_neg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:52:26.263828+00:00
-- url     : https://prove2.me/submissions/c2e44306-fc2a-4d12-9257-8ab7e26c20fb

import Mathlib.Tactic.Linarith
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict lower passage of X through -a is exactly strict upper passage
    of the sign-reversed path through a, including the infinite case. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ) :
    (fun ω => Kyprianou.Ch01.firstLowerPassage X 0 (-a) ω) =
      (fun ω => Kyprianou.Ch01.firstUpperPassage
        (fun t ω => -X t ω) a ω) := by
  classical
  funext ω
  have hset :
      ({t : ℝ≥0 | 0 < t ∧ 0 + X t ω < -a} : Set ℝ≥0) =
      ({t : ℝ≥0 | 0 < t ∧ a < -(X t ω)} : Set ℝ≥0) := by
    ext t
    constructor
    · rintro ⟨ht, hval⟩
      exact ⟨ht, by linarith⟩
    · rintro ⟨ht, hval⟩
      exact ⟨ht, by linarith⟩
  have hequiv :
      (∃ t : ℝ≥0, 0 < t ∧ 0 + X t ω < -a) ↔
      (∃ t : ℝ≥0, 0 < t ∧ a < -(X t ω)) := by
    constructor
    · rintro ⟨t, ht, hval⟩
      exact ⟨t, ht, by linarith⟩
    · rintro ⟨t, ht, hval⟩
      exact ⟨t, ht, by linarith⟩
  unfold Kyprianou.Ch01.firstLowerPassage
  unfold Kyprianou.Ch01.firstUpperPassage
  by_cases h : ∃ t : ℝ≥0, 0 < t ∧ 0 + X t ω < -a
  · simp only [dif_pos h, if_pos (hequiv.mp h), hset]
  · simp only [dif_neg h, if_neg (fun ht => h (hequiv.mpr ht))]
