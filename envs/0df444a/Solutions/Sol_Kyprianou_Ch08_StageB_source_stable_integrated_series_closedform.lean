-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_stable_integrated_series_closedform
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T01:18:34.874786+00:00
-- url     : https://prove2.me/submissions/907a6c40-d849-4704-89f8-13412b7be5dc

import Mathlib
set_option autoImplicit false

/-- Geometric closed form for the integrated stable series:
`(β(β^α − q))⁻¹ = ∑_n q^n β^{−(α(n+1)+1)}` when `q^{1/α} < β`. -/
theorem solution (α q β : ℝ) (hα : 1 < α) (hq : 0 < q)
    (hβ : q ^ (1 / α) < β) :
    (β * (β ^ α - q))⁻¹ =
      ∑' n : ℕ, q ^ n * β ^ (-(α * (n + 1) + 1)) := by
  have hα0 : α ≠ 0 := by linarith
  have hq0 : 0 ≤ q := hq.le
  have hqpow_pos : 0 < q ^ (1 / α) := Real.rpow_pos_of_pos hq (1 / α)
  have hβpos : 0 < β := lt_trans hqpow_pos hβ
  have hβα_pos : 0 < β ^ α := Real.rpow_pos_of_pos hβpos α
  have hq_lt : q < β ^ α := by
    have h1 : (q ^ (1 / α)) ^ α < β ^ α :=
      Real.rpow_lt_rpow hqpow_pos.le hβ (by linarith : (0 : ℝ) < α)
    have h2 : (q ^ (1 / α)) ^ α = q := by
      rw [← Real.rpow_mul hq0, one_div_mul_cancel hα0, Real.rpow_one]
    linarith
  have hr_nonneg : 0 ≤ q / β ^ α := div_nonneg hq0 hβα_pos.le
  have hr_lt_one : q / β ^ α < 1 := by
    rw [div_lt_one hβα_pos]
    exact hq_lt
  have hgeom : ∑' n : ℕ, (q / β ^ α) ^ n = (1 - q / β ^ α)⁻¹ := by
    apply tsum_geometric_of_norm_lt_one
    rwa [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
  have hterm : ∀ n : ℕ, q ^ n * β ^ (-(α * (n + 1) + 1)) =
      β ^ (-(α + 1)) * (q / β ^ α) ^ n := by
    intro n
    have h2 : (β ^ α) ^ n = β ^ (α * (n : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hβpos.le]
    calc q ^ n * β ^ (-(α * (n + 1) + 1))
        = q ^ n * β ^ (-(α + 1) - α * (n : ℝ)) := by
          congr 1
          congr 1
          push_cast
          ring
      _ = q ^ n * (β ^ (-(α + 1)) / β ^ (α * (n : ℝ))) := by
          rw [Real.rpow_sub hβpos]
      _ = β ^ (-(α + 1)) * (q ^ n / β ^ (α * (n : ℝ))) := by ring
      _ = β ^ (-(α + 1)) * (q / β ^ α) ^ n := by
          rw [div_pow, h2]
  have hsum : (∑' n : ℕ, q ^ n * β ^ (-(α * (n + 1) + 1))) =
      β ^ (-(α + 1)) * (1 - q / β ^ α)⁻¹ := by
    rw [show (∑' n : ℕ, q ^ n * β ^ (-(α * (n + 1) + 1)))
        = ∑' n : ℕ, β ^ (-(α + 1)) * (q / β ^ α) ^ n from tsum_congr hterm]
    rw [tsum_mul_left, hgeom]
  rw [hsum]
  have h1 : β ^ (-(α + 1)) = (β ^ α * β)⁻¹ := by
    rw [Real.rpow_neg hβpos.le, Real.rpow_add hβpos, Real.rpow_one]
  have h2 : 1 - q / β ^ α = (β ^ α - q) / β ^ α := by
    field_simp
  rw [h1, h2, inv_div]
  field_simp
