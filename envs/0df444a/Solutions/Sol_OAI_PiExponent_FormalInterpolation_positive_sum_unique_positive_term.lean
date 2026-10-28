-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.positive_sum_unique_positive_term
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:30:37.532988+00:00
-- url     : https://prove2.me/submissions/b310b21b-70bb-4ef3-accd-374b0773f17f

import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

theorem solution
    {K : Nat} [Fintype (Fin K)] (f : Fin K → Nat)
    (hunique : ∀ j k : Fin K, j ≠ k → ¬ (0 < f j ∧ 0 < f k))
    (hsum : 0 < ∑ j, f j) :
    ∃ j : Fin K, 0 < f j ∧ f j = ∑ k, f k := by
  classical
  obtain ⟨j0, hj0⟩ : ∃ j0, 0 < f j0 := by
    by_contra h
    push_neg at h
    have : ∑ j, f j = 0 := Finset.sum_eq_zero (fun j _ => Nat.le_zero.mp (h j))
    omega
  refine ⟨j0, hj0, ?_⟩
  rw [Finset.sum_eq_single j0]
  · intro k _ hk
    by_contra hne
    exact hunique j0 k (Ne.symm hk) ⟨hj0, Nat.pos_of_ne_zero hne⟩
  · intro h; exact absurd (Finset.mem_univ j0) h
