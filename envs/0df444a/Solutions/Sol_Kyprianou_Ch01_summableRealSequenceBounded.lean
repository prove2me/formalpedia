-- Prove2me | solution 1 for Kyprianou.Ch01.summableRealSequenceBounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:30:33.412718+00:00
-- url     : https://prove2.me/submissions/9f416e77-f36f-4a6c-9ff3-9494cfc647ee

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
theorem solution (a : ℕ → ℝ) (hsum : Summable a) : ∃ M, 0 ≤ M ∧ ∀ i, |a i| ≤ M := by
  have ht : Tendsto (fun i => |a i|) atTop (nhds 0) := by
    simpa using (hsum.tendsto_atTop_zero).abs
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  refine ⟨max M 0, le_max_right _ _, fun i => le_trans (hM ⟨i, rfl⟩) (le_max_left _ _)⟩

