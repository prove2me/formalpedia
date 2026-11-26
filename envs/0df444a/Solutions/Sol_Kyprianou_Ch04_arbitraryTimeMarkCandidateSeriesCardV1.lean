-- Prove2me | solution 1 for Kyprianou.Ch04.arbitraryTimeMarkCandidateSeriesCardV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:11:39.928668+00:00
-- url     : https://prove2.me/submissions/b4eb82aa-9b9c-4a05-b9d4-860b24343e7b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- Deduplicate an exact covering of the actual nonzero jumps belonging to a Borel set. -/
theorem solution (Y : NNReal → ℝ) (time : ℕ → NNReal) (mark : ℕ → ℝ)
    (hMark : ∀ k, 0 < time k → mark k = Y (time k) - Function.leftLim Y (time k))
    (hCover : ∀ u, 0 < u → Y u - Function.leftLim Y u ≠ 0 → ∃ k, time k = u)
    (D : Set (ℝ × ℝ)) :
    ({u : NNReal | 0 < u ∧ Y u - Function.leftLim Y u ≠ 0 ∧
        ((u : ℝ), Y u - Function.leftLim Y u) ∈ D}).encard =
      ∑' k : ℕ, if 0 < time k ∧ mark k ≠ 0 ∧
        ((time k : ℝ), mark k) ∈ D ∧ (∀ j : ℕ, j < k → time j ≠ time k)
      then (1 : ENNReal) else 0 := by
  classical
  let S : Set NNReal := {u | 0 < u ∧ Y u - Function.leftLim Y u ≠ 0 ∧
      ((u : ℝ), Y u - Function.leftLim Y u) ∈ D}
  have hS : S ⊆ Set.range time := fun u hu => hCover u hu.1 hu.2.1
  rw [AvramDividend.Classical.avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum time S hS]
  apply tsum_congr
  intro k
  by_cases hk : 0 < time k
  · simp [S, hk, hMark k hk, and_assoc]
  · simp [S, hk]
