-- Prove2me | solution 1 for ModernOnlineLearning.LowerBounds.probabilistic_method
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T05:09:11.827103+00:00
-- url     : https://prove2.me/submissions/6b756e8d-b088-45a0-855a-1f39df3b6f42

import Mathlib

theorem solution {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (F : Ω → ℝ) (K : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (hmean : K ≤ ∑ ω, p ω * F ω) :
    ∃ ω, 0 < p ω ∧ K ≤ F ω := by
  classical
  by_contra h
  push_neg at h
  have hpos : ∃ ω, 0 < p ω := by
    by_contra hn
    push_neg at hn
    have hz : ∀ ω, p ω = 0 := fun ω => le_antisymm (hn ω) (hp ω)
    simp [hz] at hsum
  obtain ⟨ω₀, hω₀⟩ := hpos
  have hlt : (∑ ω, p ω * F ω) < ∑ ω, p ω * K := by
    apply Finset.sum_lt_sum
    · intro ω hω
      by_cases hz : p ω = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (h ω (lt_of_le_of_ne (hp ω) (Ne.symm hz))).le (hp ω)
    · exact ⟨ω₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (h ω₀ hω₀) hω₀⟩
  rw [← Finset.sum_mul, hsum, one_mul] at hlt
  exact (not_lt_of_ge hmean) hlt

