-- Prove2me | solution 1 for Kyprianou.Ch02.truncatedAbsFinsetSumLeV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:22:39.108327+00:00
-- url     : https://prove2.me/submissions/96916571-eb8b-46e6-8b41-8d1b4ad36d6c

import Mathlib
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem _root_.solution
    {ι : Type} (S : Finset ι) (g : ι → ℝ) :
    ENNReal.ofReal (min (1 : ℝ) |∑ i ∈ S, g i|) ≤
      ∑ i ∈ S, ENNReal.ofReal (min (1 : ℝ) |g i|) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine le_trans (ENNReal.ofReal_le_ofReal (?_ : min (1:ℝ) |g a + ∑ i ∈ s, g i| ≤ min 1 |g a| + min 1 |∑ i ∈ s, g i|)) ?_
    · have h := abs_add_le (g a) (∑ i ∈ s, g i)
      have h1 := abs_nonneg (g a)
      have h2 := abs_nonneg (∑ i ∈ s, g i)
      rcases min_cases (1:ℝ) |g a| with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
        rcases min_cases (1:ℝ) |∑ i ∈ s, g i| with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e1, e2] <;>
        rcases min_cases (1:ℝ) |g a + ∑ i ∈ s, g i| with ⟨e3, _⟩ | ⟨e3, _⟩ <;> rw [e3] <;> linarith
    · rw [ENNReal.ofReal_add (le_min zero_le_one (abs_nonneg _)) (le_min zero_le_one (abs_nonneg _))]
      exact add_le_add le_rfl ih

