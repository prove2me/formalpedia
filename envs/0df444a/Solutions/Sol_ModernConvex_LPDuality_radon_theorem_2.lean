-- Prove2me | solution 2 for ModernConvex.LPDuality.radon_theorem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:27:47.01675+00:00
-- url     : https://prove2.me/submissions/917cc6c8-117a-429c-9dbb-d47b652c50ff

import Mathlib
set_option autoImplicit false
open Classical in
theorem solution {n m : ℕ} (a : Fin m → Fin n → ℝ) (hm : n + 2 ≤ m) :
    ∃ I J : Finset (Fin m), I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ I ∪ J = Finset.univ ∧
      (convexHull ℝ (a '' (I : Set (Fin m))) ∩ convexHull ℝ (a '' (J : Set (Fin m)))).Nonempty := by
  have hdep : ¬ AffineIndependent ℝ a := by
    intro h
    have := h.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range a))
    simp at this h2
    omega
  obtain ⟨I, p, hpI, hpJ⟩ := Convex.radon_partition hdep
  refine ⟨I.toFinset, Iᶜ.toFinset, ?_, ?_, ?_, ?_, ⟨p, ?_, ?_⟩⟩
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Set.toFinset_eq_empty] at hne
    simp [hne] at hpI
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Set.toFinset_eq_empty] at hne
    simp [hne] at hpJ
  · simp [Finset.disjoint_left]
  · ext x; simp [Classical.em]
  · simpa using hpI
  · simpa using hpJ
