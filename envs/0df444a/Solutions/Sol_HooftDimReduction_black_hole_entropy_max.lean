-- Prove2me | solution 1 for HooftDimReduction.black_hole_entropy_max
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T15:43:23.626006+00:00
-- url     : https://prove2.me/submissions/67a0d3c0-0f54-47da-9762-d982b984e704

import Mathlib

theorem hooft_bh_entropy_aux {ι : Type} (s : Finset ι) (M : ι → ℝ)
    (hM : ∀ i ∈ s, 0 ≤ M i) (R : ℝ) (hfit : 2 * ∑ i ∈ s, M i < R) :
    ∑ i ∈ s, 4 * Real.pi * M i ^ 2 < (4 * Real.pi * R ^ 2) / 4 ∧
      ∀ ε : ℝ, 0 < ε → ∃ m : ℝ, 0 ≤ m ∧ 2 * m < R ∧
        (4 * Real.pi * R ^ 2) / 4 - ε < 4 * Real.pi * m ^ 2 := by
  have hS0 : 0 ≤ ∑ i ∈ s, M i := Finset.sum_nonneg hM
  have hR : 0 < R := by linarith
  have hpi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · have h1 : ∑ i ∈ s, M i ^ 2 ≤ ∑ i ∈ s, M i * ∑ j ∈ s, M j := by
      apply Finset.sum_le_sum
      intro i hi
      rw [sq]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hM hi) (hM i hi)
    rw [← Finset.sum_mul] at h1
    have h2 : (∑ i ∈ s, M i) * (∑ i ∈ s, M i) < (R / 2) * (R / 2) :=
      mul_self_lt_mul_self hS0 (by linarith)
    rw [← Finset.mul_sum]
    have : ∑ i ∈ s, M i ^ 2 < R ^ 2 / 4 := by nlinarith
    nlinarith
  · intro ε hε
    set t := min (R / 4) (ε / (8 * Real.pi * R)) with ht
    have ht0 : 0 < t := lt_min (by linarith) (by positivity)
    have ht1 : t ≤ R / 4 := min_le_left _ _
    have ht2 : t ≤ ε / (8 * Real.pi * R) := min_le_right _ _
    have ht3 : 8 * Real.pi * R * t ≤ ε := by
      rw [le_div_iff₀ (by positivity)] at ht2; linarith
    refine ⟨R / 2 - t, by linarith, by linarith, ?_⟩
    nlinarith [sq_nonneg t]

theorem solution {ι : Type} (s : Finset ι) (M : ι → ℝ)
    (hM : ∀ i ∈ s, 0 ≤ M i) (R : ℝ) (hfit : 2 * ∑ i ∈ s, M i < R) :
    ∑ i ∈ s, 4 * Real.pi * M i ^ 2 < (4 * Real.pi * R ^ 2) / 4 ∧
      ∀ ε : ℝ, 0 < ε → ∃ m : ℝ, 0 ≤ m ∧ 2 * m < R ∧
        (4 * Real.pi * R ^ 2) / 4 - ε < 4 * Real.pi * m ^ 2 := by
  exact hooft_bh_entropy_aux s M hM R hfit
