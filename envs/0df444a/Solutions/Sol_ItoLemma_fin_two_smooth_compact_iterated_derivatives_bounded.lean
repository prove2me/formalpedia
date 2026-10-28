-- Prove2me | solution 1 for ItoLemma.fin_two_smooth_compact_iterated_derivatives_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:43:46.749457+00:00
-- url     : https://prove2.me/submissions/b6b4b10f-7c2b-4569-a107-6ab1a62e8610

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Group.Bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Smooth compact support yields a single uniform bound for derivatives
of order at most two on the two-dimensional state space. -/
theorem solution
    (f : (Fin 2 → ℝ) → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : ℕ, i ≤ 2 → ∀ z : Fin 2 → ℝ, ‖iteratedFDeriv ℝ i f z‖ ≤ C := by
  have horder (i : ℕ) :
      (↑i : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.mpr (le_top : (i : ℕ∞) ≤ ⊤)
  have hbound (i : ℕ) :
      ∃ B : ℝ, ∀ z : Fin 2 → ℝ, ‖iteratedFDeriv ℝ i f z‖ ≤ B := by
    exact (hs.iteratedFDeriv i).exists_bound_of_continuous
      (hf.continuous_iteratedFDeriv (horder i))
  obtain ⟨B₀, h₀⟩ := hbound 0
  obtain ⟨B₁, h₁⟩ := hbound 1
  obtain ⟨B₂, h₂⟩ := hbound 2
  refine ⟨max (max 0 B₀) (max B₁ B₂),
    (le_max_left 0 B₀).trans (le_max_left _ _), ?_⟩
  intro i hi z
  have hc : i = 0 ∨ i = 1 ∨ i = 2 := by
    rcases Nat.of_le_succ hi with hi1 | hi2
    · rcases Nat.of_le_succ hi1 with hi0 | hi1eq
      · exact Or.inl (Nat.eq_zero_of_le_zero hi0)
      · exact Or.inr (Or.inl hi1eq)
    · exact Or.inr (Or.inr hi2)
  rcases hc with rfl | rfl | rfl
  · exact (h₀ z).trans ((le_max_right 0 B₀).trans (le_max_left _ _))
  · exact (h₁ z).trans ((le_max_left B₁ B₂).trans (le_max_right _ _))
  · exact (h₂ z).trans ((le_max_right B₁ B₂).trans (le_max_right _ _))
