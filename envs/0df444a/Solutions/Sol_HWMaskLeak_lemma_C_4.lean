-- Prove2me | solution 1 for HWMaskLeak.lemma_C_4
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:28:01.852387+00:00
-- url     : https://prove2.me/submissions/95e9b22b-9949-41cf-b2e7-ec39a0572ee2

import Mathlib
namespace HWMaskLeak

theorem lemma_C_4 (n : ℕ) (α β : ℝ) :
    ((n : ℝ) - 1) / 10 * Real.sin α ^ 2 ≤ ∑ j ∈ Finset.range n, Real.sin (α + 2 ^ j * β) ^ 2 := by
  have pair : ∀ θ : ℝ, Real.sin α ^ 2 ≤ 5 * (Real.sin (α + θ) ^ 2 + Real.sin (α + 2 * θ) ^ 2) := by
    intro θ
    set x := α + θ with hx
    set y := α + 2 * θ with hy
    have hα : α = 2 * x - y := by rw [hx, hy]; ring
    have hs : Real.sin α = 2 * Real.sin x * Real.cos x * Real.cos y - Real.cos (2 * x) * Real.sin y := by
      rw [hα, Real.sin_sub, Real.sin_two_mul]
    have h1 : |Real.sin α| ≤ 2 * |Real.sin x| + |Real.sin y| := by
      rw [hs]
      have a1 : |2 * Real.sin x * Real.cos x * Real.cos y| ≤ 2 * |Real.sin x| := by
        rw [abs_mul, abs_mul, abs_mul, abs_two]
        have hc : |Real.cos x| * |Real.cos y| ≤ 1 :=
          mul_le_one₀ (Real.abs_cos_le_one x) (abs_nonneg _) (Real.abs_cos_le_one y)
        nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg (Real.sin x))]
      have a2 : |Real.cos (2 * x) * Real.sin y| ≤ |Real.sin y| := by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
      calc _ ≤ _ := abs_sub _ _
        _ ≤ _ := add_le_add a1 a2
    have h2 : Real.sin α ^ 2 ≤ (2 * |Real.sin x| + |Real.sin y|) ^ 2 := by
      rw [← sq_abs (Real.sin α)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (|Real.sin x| - 2 * |Real.sin y|), sq_abs (Real.sin x), sq_abs (Real.sin y)]
  rcases n with _ | m
  · simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
    nlinarith [sq_nonneg (Real.sin α)]
  · set f : ℕ → ℝ := fun j => Real.sin (α + 2 ^ j * β) ^ 2 with hf
    have hf0 : ∀ j, 0 ≤ f j := fun j => sq_nonneg _
    have hA : ∑ j ∈ Finset.range m, f j ≤ ∑ j ∈ Finset.range (m + 1), f j := by
      rw [Finset.sum_range_succ]; linarith [hf0 m]
    have hB : ∑ j ∈ Finset.range m, f (j + 1) ≤ ∑ j ∈ Finset.range (m + 1), f j := by
      rw [Finset.sum_range_succ']; linarith [hf0 0]
    have hC : ∑ j ∈ Finset.range m, Real.sin α ^ 2 / 5 ≤ ∑ j ∈ Finset.range m, (f j + f (j + 1)) := by
      apply Finset.sum_le_sum
      intro j _
      have := pair (2 ^ j * β)
      have e : α + 2 * (2 ^ j * β) = α + 2 ^ (j + 1) * β := by rw [pow_succ]; ring
      rw [e] at this
      simp only [hf]
      linarith
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib] at hC
    push_cast
    show ((m : ℝ) + 1 - 1) / 10 * Real.sin α ^ 2 ≤ ∑ j ∈ Finset.range (m + 1), f j
    have : ((m : ℝ) + 1 - 1) / 10 * Real.sin α ^ 2 = (m * (Real.sin α ^ 2 / 5)) / 2 := by ring
    rw [this]
    linarith

end HWMaskLeak

theorem solution (n : ℕ) (α β : ℝ) :
    ((n : ℝ) - 1) / 10 * Real.sin α ^ 2 ≤ ∑ j ∈ Finset.range n, Real.sin (α + 2 ^ j * β) ^ 2 :=
  HWMaskLeak.lemma_C_4 n α β
