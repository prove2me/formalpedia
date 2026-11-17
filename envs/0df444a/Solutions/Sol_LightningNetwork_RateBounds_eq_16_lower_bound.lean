-- Prove2me | solution 1 for LightningNetwork.RateBounds.eq_16_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T15:35:10.857815+00:00
-- url     : https://prove2.me/submissions/32c777e0-cc89-40b1-92de-da4641576e59

import Mathlib

theorem solution (B C α κ : ℝ) (hB : 0 < B) (hC : 0 < C) (hα0 : 0 < α) (hα1 : α < 1)
    (hκ : α ^ 2 / (B * (1 - α)) ≤ κ) :
    (∀ κ' : ℝ, 0 < κ' → -C / κ' < C / (1 - Real.exp κ')) ∧
      α / κ ≤ 2 * B / (B * κ + Real.sqrt (B * κ * (B * κ + 4))) := by
  constructor
  · intro κ' hκ'
    have hE : κ' + 1 < Real.exp κ' := Real.add_one_lt_exp (ne_of_gt hκ')
    have hE1 : κ' < Real.exp κ' - 1 := by linarith
    have hpos1 : 0 < Real.exp κ' - 1 := by linarith
    have hlt : C / (Real.exp κ' - 1) < C / κ' := by
      rw [div_lt_div_iff₀ hpos1 hκ']
      nlinarith [hE1, hC]
    have hEq : C / (1 - Real.exp κ') = -(C / (Real.exp κ' - 1)) := by
      rw [show 1 - Real.exp κ' = -(Real.exp κ' - 1) by ring, div_neg]
    have hneg : -C / κ' = -(C / κ') := by ring
    rw [hEq, hneg]
    linarith
  · have h1α : 0 < 1 - α := by linarith
    have hden0 : 0 < B * (1 - α) := mul_pos hB h1α
    have hκpos : 0 < κ := lt_of_lt_of_le (div_pos (pow_pos hα0 2) hden0) hκ
    have hBκ : 0 < B * κ := mul_pos hB hκpos
    have hs : α ^ 2 / (1 - α) ≤ B * κ := by
      have h2 := mul_le_mul_of_nonneg_right hκ hB.le
      have h3 : α ^ 2 / (B * (1 - α)) * B = α ^ 2 / (1 - α) := by
        field_simp
      rw [h3] at h2
      linarith [h2]
    have hkey : α * Real.sqrt (B * κ * (B * κ + 4)) ≤ B * κ * (2 - α) := by
      have hsq : (α * Real.sqrt (B * κ * (B * κ + 4))) ^ 2 ≤ (B * κ * (2 - α)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have h4 : α ^ 2 ≤ B * κ * (1 - α) := by
          rw [div_le_iff₀ h1α] at hs
          linarith [hs]
        nlinarith [h4, hBκ, hα0, hα1]
      have hnn : 0 ≤ α * Real.sqrt (B * κ * (B * κ + 4)) := by positivity
      have hnn2 : 0 ≤ B * κ * (2 - α) := by nlinarith
      have habs : |α * Real.sqrt (B * κ * (B * κ + 4))| ≤ |B * κ * (2 - α)| :=
        sq_le_sq.mp hsq
      rwa [abs_of_nonneg hnn, abs_of_nonneg hnn2] at habs
    have hdenpos : 0 < B * κ + Real.sqrt (B * κ * (B * κ + 4)) := by positivity
    rw [div_le_div_iff₀ hκpos hdenpos]
    nlinarith [hkey]
