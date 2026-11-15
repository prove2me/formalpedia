-- Prove2me | solution 1 for Kyprianou.Ch01.cadlag_nnreal_neg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T20:58:46.443249+00:00
-- url     : https://prove2.me/submissions/02b3b122-eb32-4b85-b93c-ca5814f8f8fb

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (hf : ProbabilityTheory.IsCadlag f) :
    ProbabilityTheory.IsCadlag (fun s => -f s) := by
  intro t
  change ContinuousWithinAt (fun s => -f s) (Set.Ici t) t ∧
    ∃ l : ℝ, Tendsto (fun s => -f s)
      (nhdsWithin t (Set.Iio t)) (nhds l)
  constructor
  · exact (hf t).1.neg
  · obtain ⟨l, hl⟩ := (hf t).2
    exact ⟨-l, hl.neg⟩
