-- Prove2me | solution 1 for KhintchineTwoRegime.theorem_2_q_bounds
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T03:04:41.1738+00:00
-- url     : https://prove2.me/submissions/918def13-f13d-4e15-aa4b-ceacad799a97

import Mathlib

namespace P2MHole01_a75860af
theorem solution : ((2 : ℝ) - √((2 : ℝ) - √(2 : ℝ)) ^ (2 : ℕ)) / √(2 : ℝ) = (1 : ℝ) := by
  norm_num
end P2MHole01_a75860af

/-- The lower endpoint d0 = √(2 − √2) of the τ-interval maps to q = 1. -/
lemma endpoint_d0 : (2 - Real.sqrt (2 - Real.sqrt 2) ^ 2) / Real.sqrt 2 = 1 := by
  (first | exact P2MHole01_a75860af.solution | (apply P2MHole01_a75860af.solution <;> assumption))

namespace P2MHole02_fd60206f
theorem solution :
  ((2 : ℝ) - √((2 : ℝ) - √(966 : ℝ) / (22 : ℝ)) ^ (2 : ℕ)) / √(2 : ℝ) = √(483 : ℝ) / (22 : ℝ) := by
  -- the radicand 2 - √966/22 is nonnegative, so (√ ·)^2 unfolds
  have h_inner_nonneg : 0 ≤ (2 : ℝ) - √(966 : ℝ) / (22 : ℝ) := by
    have h : √(966 : ℝ) ≤ (44 : ℝ) := by
      rw [Real.sqrt_le_iff]
      norm_num
    linarith [h, show (2 : ℝ) = 44 / 22 by norm_num]
  rw [Real.sq_sqrt h_inner_nonneg]   -- (2 - (2 - √966/22))/√2
  rw [sub_sub_self]                  -- (√966/22)/√2
  have h966 : √(966 : ℝ) = √(483 : ℝ) * √(2 : ℝ) := by
    have : (966 : ℝ) = 483 * 2 := by norm_num
    rw [this, Real.sqrt_mul (by norm_num : 0 ≤ (483 : ℝ))]
  rw [h966]
  field_simp
end P2MHole02_fd60206f

-- riskiest
/-- The upper endpoint d1 = √(2 − √966/22) of the τ-interval maps to q = √483/22
    (uses √966 = √483 · √2 since 966 = 483 · 2). -/
lemma endpoint_d1 :
    (2 - Real.sqrt (2 - Real.sqrt 966 / 22) ^ 2) / Real.sqrt 2 = Real.sqrt 483 / 22 := by
  (first | exact P2MHole02_fd60206f.solution | (apply P2MHole02_fd60206f.solution <;> assumption))

namespace P2MHole03_a04480cb
theorem solution (τ : ℝ) (h0 : (0 : ℝ) ≤ τ) (hhi : τ ≤ √((2 : ℝ) - √(966 : ℝ) / (22 : ℝ))) :
  ((2 : ℝ) - √((2 : ℝ) - √(966 : ℝ) / (22 : ℝ)) ^ (2 : ℕ)) / √(2 : ℝ) ≤ ((2 : ℝ) - τ ^ (2 : ℕ)) / √(2 : ℝ) := by
  bound
end P2MHole03_a04480cb

/-- q = (2 − τ²)/√2 decreases in τ ≥ 0, so τ ≤ d1 gives q(d1) ≤ q(τ),
    where d1 = √(2 − √966/22). -/
lemma q_low (τ : ℝ) (h0 : 0 ≤ τ)
    (hhi : τ ≤ Real.sqrt (2 - Real.sqrt 966 / 22)) :
    (2 - Real.sqrt (2 - Real.sqrt 966 / 22) ^ 2) / Real.sqrt 2 ≤ (2 - τ ^ 2) / Real.sqrt 2 := by
  (first | exact P2MHole03_a04480cb.solution τ h0 hhi | (apply P2MHole03_a04480cb.solution <;> assumption))

namespace P2MHole04_63da9922
theorem solution (τ : ℝ) (hlo : √((2 : ℝ) - √(2 : ℝ)) ≤ τ) :
  ((2 : ℝ) - τ ^ (2 : ℕ)) / √(2 : ℝ) ≤ ((2 : ℝ) - √((2 : ℝ) - √(2 : ℝ)) ^ (2 : ℕ)) / √(2 : ℝ) := by
  bound
end P2MHole04_63da9922

/-- q decreases in τ ≥ 0, so d0 ≤ τ (with d0 = √(2 − √2)) gives q(τ) ≤ q(d0). -/
lemma q_high (τ : ℝ) (hlo : Real.sqrt (2 - Real.sqrt 2) ≤ τ) :
    (2 - τ ^ 2) / Real.sqrt 2 ≤ (2 - Real.sqrt (2 - Real.sqrt 2) ^ 2) / Real.sqrt 2 := by
  (first | exact P2MHole04_63da9922.solution τ hlo | (apply P2MHole04_63da9922.solution <;> assumption))

theorem solution (τ : ℝ)
    (hτ : τ ∈ Set.Icc (Real.sqrt (2 - Real.sqrt 2)) (Real.sqrt (2 - Real.sqrt 966 / 22))) :
    0 ≤ τ ∧ Real.sqrt 483 / 22 ≤ (2 - τ ^ 2) / Real.sqrt 2 ∧
      (2 - τ ^ 2) / Real.sqrt 2 ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := hτ
  have h0 : 0 ≤ τ := by linarith [Real.sqrt_nonneg (2 - Real.sqrt 2)]
  have hlow : (2 - Real.sqrt (2 - Real.sqrt 966 / 22) ^ 2) / Real.sqrt 2 ≤
      (2 - τ ^ 2) / Real.sqrt 2 := q_low τ h0 hhi
  have hhigh : (2 - τ ^ 2) / Real.sqrt 2 ≤
      (2 - Real.sqrt (2 - Real.sqrt 2) ^ 2) / Real.sqrt 2 := q_high τ hlo
  have hq2 : (2 - Real.sqrt (2 - Real.sqrt 966 / 22) ^ 2) / Real.sqrt 2 = Real.sqrt 483 / 22 :=
    endpoint_d1
  have hq1 : (2 - Real.sqrt (2 - Real.sqrt 2) ^ 2) / Real.sqrt 2 = 1 := endpoint_d0
  refine ⟨h0, ?_, ?_⟩
  · linarith [hlow, hq2]
  · linarith [hhigh, hq1]
