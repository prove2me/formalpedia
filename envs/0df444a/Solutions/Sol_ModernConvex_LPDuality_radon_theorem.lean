-- Prove2me | solution 1 for ModernConvex.LPDuality.radon_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:58:02.840367+00:00
-- url     : https://prove2.me/submissions/8293890c-817d-4da6-bd1d-b05300f0a3a1

import Mathlib

theorem solution {n m : ℕ} (a : Fin m → Fin n → ℝ) (hm : n + 2 ≤ m) :
    ∃ I J : Finset (Fin m), I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ I ∪ J = Finset.univ ∧
      (convexHull ℝ (a '' (I : Set (Fin m))) ∩ convexHull ℝ (a '' (J : Set (Fin m)))).Nonempty := by
  classical
  have hni : ¬ AffineIndependent ℝ a := by
    intro h
    have := h.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range a))
    simp at this h2
    omega
  obtain ⟨I, hI⟩ := Convex.radon_partition hni
  refine ⟨I.toFinset, Iᶜ.toFinset, ?_, ?_, ?_, ?_, ?_⟩
  · rcases Set.eq_empty_or_nonempty I with h | h
    · subst h; simp at hI
    · simpa using h
  · rcases Set.eq_empty_or_nonempty Iᶜ with h | h
    · rw [h] at hI; simp at hI
    · obtain ⟨x, hx⟩ := h; exact ⟨x, by simpa using hx⟩
  · rw [Finset.disjoint_iff_ne]; intro x hx y hy; simp at hx hy; rintro rfl; exact hy hx
  · ext x; simp
  · simpa using hI
