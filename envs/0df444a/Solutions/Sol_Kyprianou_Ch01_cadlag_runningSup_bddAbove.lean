-- Prove2me | solution 1 for Kyprianou.Ch01.cadlag_runningSup_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:37:11.735921+00:00
-- url     : https://prove2.me/submissions/9d7a92fc-7c3d-4c5d-8eeb-9d873e8f2927

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (hf : ProbabilityTheory.IsCadlag f) (T : ℝ≥0) :
    BddAbove {z : ℝ | ∃ s : ℝ≥0, s ≤ T ∧ z = f s} := by
  have hr : ∀ t, Tendsto f (nhdsWithin t (Set.Ici t)) (nhds (f t)) := by
    intro t
    exact (hf t).1
  have hl : ∀ t, ∃ l : ℝ, Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l) := by
    intro t
    exact (hf t).2
  have hbounded :=
    AvramDividend.Classical.one_sided_limits_bddAbove_Icc f hr hl T
  have heq :
      {z : ℝ | ∃ s : ℝ≥0, s ≤ T ∧ z = f s} =
      Set.range (fun s : Set.Icc (0 : ℝ≥0) T => f s.1) := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, (zero_le : (0 : ℝ≥0) ≤ s), hs⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2.2, rfl⟩
  simpa only [heq] using hbounded

