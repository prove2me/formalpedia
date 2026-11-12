-- Prove2me | solution 1 for HWMaskLeak.eq_36
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T16:22:39.230882+00:00
-- url     : https://prove2.me/submissions/51f36930-6b19-4598-b824-833a0db885b7

import Mathlib

set_option autoImplicit false

/-- A telescoping-product inequality for unimodular complex numbers. -/
theorem solution (ζ ξ : ℂ) (hζ : ‖ζ‖ = 1) (hξ : ‖ξ‖ = 1) (k : ℕ) :
    ‖(1 - ξ) * ∏ j ∈ Finset.range k, (1 + ζ * ξ ^ (2 ^ j))‖
      ≤ 2 + 2 ^ (k + 1) * ‖1 - ζ‖ := by
  classical
  let P : ℕ → ℂ := fun n => (1 - ξ) * ∏ j ∈ Finset.range n, (1 + ζ * ξ ^ (2 ^ j))
  have hPsucc : ∀ n, P (n + 1) = P n * (1 + ζ * ξ ^ (2 ^ n)) := by
    intro n
    dsimp only [P]
    rw [Finset.prod_range_succ]
    ring
  have hpow : ∀ n, ξ ^ (2 ^ (n + 1)) = (ξ ^ (2 ^ n)) ^ 2 := by
    intro n
    rw [show 2 ^ (n + 1) = 2 ^ n * 2 by ring]
    rw [pow_mul]
  have aux : ∀ n, ∃ R : ℂ,
      P n = (1 - ξ ^ (2 ^ n)) + (ζ - 1) * R ∧
        ‖R‖ ≤ (2 : ℝ) ^ (n + 1) - 2 := by
    intro n
    induction n with
    | zero =>
        refine ⟨0, ?_, ?_⟩
        · simp [P]
        · norm_num
    | succ n ih =>
        obtain ⟨R, hR, hRb⟩ := ih
        refine ⟨(1 - ξ ^ (2 ^ n)) * ξ ^ (2 ^ n) + R * (1 + ζ * ξ ^ (2 ^ n)), ?_, ?_⟩
        · rw [hPsucc n, hR, hpow n]
          ring
        · have ha : ‖ξ ^ (2 ^ n)‖ = 1 := by rw [norm_pow, hξ, one_pow]
          have hterm1 : ‖(1 - ξ ^ (2 ^ n)) * ξ ^ (2 ^ n)‖ ≤ 2 := by
            rw [norm_mul, ha, mul_one]
            calc ‖1 - ξ ^ (2 ^ n)‖ ≤ ‖(1 : ℂ)‖ + ‖ξ ^ (2 ^ n)‖ := norm_sub_le _ _
              _ = 2 := by rw [ha]; norm_num
          have hterm2 : ‖1 + ζ * ξ ^ (2 ^ n)‖ ≤ 2 := by
            calc ‖1 + ζ * ξ ^ (2 ^ n)‖ ≤ ‖(1 : ℂ)‖ + ‖ζ * ξ ^ (2 ^ n)‖ := norm_add_le _ _
              _ = 2 := by rw [norm_mul, hζ, ha, one_mul]; norm_num
          have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
            have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
              (by omega : 1 ≤ n + 1)
            simpa using h
          have hRnonneg : 0 ≤ (2 : ℝ) ^ (n + 1) - 2 := by linarith
          calc ‖(1 - ξ ^ (2 ^ n)) * ξ ^ (2 ^ n) + R * (1 + ζ * ξ ^ (2 ^ n))‖
              ≤ ‖(1 - ξ ^ (2 ^ n)) * ξ ^ (2 ^ n)‖ +
                  ‖R * (1 + ζ * ξ ^ (2 ^ n))‖ := norm_add_le _ _
            _ ≤ 2 + ((2 : ℝ) ^ (n + 1) - 2) * 2 := by
                apply add_le_add hterm1
                rw [norm_mul]
                exact mul_le_mul hRb hterm2 (norm_nonneg _) hRnonneg
            _ = (2 : ℝ) ^ (n + 2) - 2 := by
                rw [show (2 : ℝ) ^ (n + 2) = 2 ^ (n + 1) * 2 by ring]
                ring
  obtain ⟨R, hPR, hRb⟩ := aux k
  change ‖P k‖ ≤ 2 + 2 ^ (k + 1) * ‖1 - ζ‖
  rw [hPR]
  calc ‖(1 - ξ ^ (2 ^ k)) + (ζ - 1) * R‖
      ≤ ‖1 - ξ ^ (2 ^ k)‖ + ‖(ζ - 1) * R‖ := norm_add_le _ _
    _ = ‖1 - ξ ^ (2 ^ k)‖ + ‖1 - ζ‖ * ‖R‖ := by
        have hζ1 : ‖ζ - 1‖ = ‖1 - ζ‖ := by
          rw [show ζ - 1 = -(1 - ζ) by ring, norm_neg]
        rw [norm_mul, hζ1]
    _ ≤ 2 + ‖1 - ζ‖ * ((2 : ℝ) ^ (k + 1) - 2) := by
        apply add_le_add
        · calc ‖1 - ξ ^ (2 ^ k)‖ ≤ ‖(1 : ℂ)‖ + ‖ξ ^ (2 ^ k)‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_pow, hξ, one_pow]; norm_num
        · exact mul_le_mul_of_nonneg_left hRb (norm_nonneg _)
    _ ≤ 2 + 2 ^ (k + 1) * ‖1 - ζ‖ := by
        have hz : 0 ≤ ‖1 - ζ‖ := norm_nonneg _
        have h2 : (0 : ℝ) ≤ 2 ^ (k + 1) := by positivity
        nlinarith
