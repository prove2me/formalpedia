-- Prove2me | solution 1 for MultiPriceOnline.Ratios.two_price_formula
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:48:48.394004+00:00
-- url     : https://prove2.me/submissions/f47c6018-2ee0-4b72-a14f-1d15b76cd9e4

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

set_option autoImplicit false

theorem solution (r : ℕ → ℝ) (ξ : ℝ) (hr1 : 0 < r 1) (hξ : 1 < ξ)
    (hr2 : r 2 = ξ * r 1) (α : ℕ → ℝ) (hα : MultiPriceOnline.Balance.IsBookingLimits 2 r α) :
    MultiPriceOnline.Ranking.F α = 1 - (Real.sqrt (1 + 4 * ξ * (ξ - 1) / Real.exp 1) - 1) / (2 * (ξ - 1)) ∧
    α 1 = Real.log (1 / (1 - (1 - (Real.sqrt (1 + 4 * ξ * (ξ - 1) / Real.exp 1) - 1) /
      (2 * (ξ - 1))))) := by
  obtain ⟨hpos, hsum, h7⟩ := hα
  have hsum2 : α 1 + α 2 = 1 := by
    have : Finset.Icc 1 2 = {1, 2} := by decide
    rw [this, Finset.sum_pair (by norm_num)] at hsum
    exact hsum
  have h := h7 2 le_rfl le_rfl
  have hc : 1 - r (2 - 1) / r 2 = (ξ - 1) / ξ := by
    have : (2 - 1 : ℕ) = 1 := rfl
    rw [this, hr2]
    have : ξ ≠ 0 := by linarith
    field_simp
  rw [hc] at h
  have hξ0 : 0 < ξ := by linarith
  have hξ1 : 0 < ξ - 1 := by linarith
  set w : ℝ := Real.exp (-α 1) with hw
  set P : ℝ := Real.exp (α 1) with hP
  set e : ℝ := Real.exp 1 with he
  have hwpos : 0 < w := Real.exp_pos _
  have hepos : 0 < e := Real.exp_pos _
  have hPpos : 0 < P := Real.exp_pos _
  have hPw : P * w = 1 := by
    rw [hP, hw, ← Real.exp_add]; simp
  have h2 : Real.exp (-α 2) = P / e := by
    have : -α 2 = α 1 - 1 := by linarith
    rw [this, Real.exp_sub]
  rw [h2] at h
  have h' : (1 - w) * (ξ - 1) * e = ξ * (e - P) := by
    rw [eq_div_iff (by positivity)] at h
    field_simp at h
    linear_combination h
  have Q' : (ξ - 1) * e * w ^ 2 + e * w - ξ = 0 := by
    linear_combination (-w) * h' + ξ * hPw
  have Q : (ξ - 1) * w ^ 2 + w = ξ / e := by
    rw [eq_div_iff hepos.ne']
    linarith
  have hD : 1 + 4 * ξ * (ξ - 1) / e = (2 * (ξ - 1) * w + 1) ^ 2 := by
    have : 4 * ξ * (ξ - 1) / e = 4 * (ξ - 1) * (ξ / e) := by ring
    rw [this, ← Q]; ring
  have hs : Real.sqrt (1 + 4 * ξ * (ξ - 1) / e) = 2 * (ξ - 1) * w + 1 := by
    rw [hD]
    exact Real.sqrt_sq (by positivity)
  have hX : (Real.sqrt (1 + 4 * ξ * (ξ - 1) / e) - 1) / (2 * (ξ - 1)) = w := by
    rw [hs]; field_simp; ring
  rw [hX]
  refine ⟨?_, ?_⟩
  · show 1 - Real.exp (-α 1) = 1 - w
    rfl
  · have : 1 - (1 - w) = w := by ring
    rw [this, one_div, hw, ← Real.exp_neg, neg_neg, Real.log_exp]
