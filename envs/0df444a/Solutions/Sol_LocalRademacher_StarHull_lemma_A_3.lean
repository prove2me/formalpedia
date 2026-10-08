-- Prove2me | solution 1 for LocalRademacher.StarHull.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:11:05.644096+00:00
-- url     : https://prove2.me/submissions/3e9dc012-67ed-42e6-bdea-79ad12d86fe8

import Mathlib

theorem solution :
    (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → Real.sqrt (u + v) ≤ Real.sqrt u + Real.sqrt v) ∧
      ∀ u v α : ℝ, 0 ≤ u → 0 ≤ v → 0 < α → 2 * Real.sqrt (u * v) ≤ α * u + v / α := by
  refine ⟨fun u v hu hv => ?_, fun u v α hu hv hα => ?_⟩
  · rw [Real.sqrt_le_iff]
    have h1 := Real.sq_sqrt hu
    have h2 := Real.sq_sqrt hv
    have h3 := Real.sqrt_nonneg u
    have h4 := Real.sqrt_nonneg v
    constructor
    · positivity
    · nlinarith [mul_nonneg h3 h4]
  · rw [Real.sqrt_mul hu]
    have h1 := Real.sq_sqrt hu
    have h2 := Real.sq_sqrt hv
    have key : 2 * (Real.sqrt u * Real.sqrt v) * α ≤ α * u * α + v := by
      have e : α * u * α + v - 2 * (Real.sqrt u * Real.sqrt v) * α
          = (α * Real.sqrt u - Real.sqrt v) ^ 2 := by
        linear_combination (-α ^ 2) * h1 - h2
      nlinarith [sq_nonneg (α * Real.sqrt u - Real.sqrt v)]
    have : α * u + v / α = (α * u * α + v) / α := by
      field_simp
    rw [this, le_div_iff₀ hα]
    linarith
