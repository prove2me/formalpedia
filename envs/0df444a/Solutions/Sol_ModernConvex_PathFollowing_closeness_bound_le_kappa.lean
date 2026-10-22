-- Prove2me | solution 1 for ModernConvex.PathFollowing.closeness_bound_le_kappa
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:56:16.808563+00:00
-- url     : https://prove2.me/submissions/130edf56-dae3-4361-83ff-7db28af55714

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder
open ModernConvex.PathFollowing

theorem g69a2_cb (s κ χ r : ℝ) (hs : 1 ≤ s) (hχ : 0 < χ) (hχκ : χ ≤ κ)
    (hκ : κ ≤ 0.1) (hr : r = Real.sqrt (χ ^ 2 + κ ^ 2) / (1 - κ)) :
    r * (1 + r) / (1 - χ / s) * (χ / s + r / (1 - r) + κ / (1 - κ)) ≤ κ := by
  have hκ0 : 0 < κ := lt_of_lt_of_le hχ hχκ
  have ha0 : 0 < χ / s := div_pos hχ (by linarith)
  have ha1 : χ / s ≤ κ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hsq : Real.sqrt (χ ^ 2 + κ ^ 2) ≤ 1.42 * κ := by
    rw [Real.sqrt_le_iff]; constructor
    · linarith
    · nlinarith
  have hr0 : 0 ≤ r := by rw [hr]; apply div_nonneg (Real.sqrt_nonneg _); linarith
  have hr1 : r ≤ 1.58 * κ := by
    rw [hr, div_le_iff₀ (by linarith)]; nlinarith
  have hT1 : r * (1 + r) / (1 - χ / s) ≤ 2.04 * κ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hT1' : 0 ≤ r * (1 + r) / (1 - χ / s) := by
    apply div_nonneg (by positivity); linarith
  have hb : r / (1 - r) ≤ 1.9 * κ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hc : κ / (1 - κ) ≤ 1.12 * κ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hT2 : χ / s + r / (1 - r) + κ / (1 - κ) ≤ 4.02 * κ := by linarith
  have hT2' : 0 ≤ χ / s + r / (1 - r) + κ / (1 - κ) := by
    have : 0 ≤ r / (1 - r) := div_nonneg hr0 (by linarith)
    have : 0 ≤ κ / (1 - κ) := div_nonneg hκ0.le (by linarith)
    linarith
  calc _ ≤ (2.04 * κ) * (4.02 * κ) := mul_le_mul hT1 hT2 hT2' (by linarith)
    _ ≤ κ := by nlinarith


/-- Ben-Tal–Nemirovski, p. 421, after (6.5.73): if `0 < χ ≤ κ ≤ 0.1`, the right-hand side of
(6.5.73), `ρ(1+ρ)/(1 − χk^{-1/2}) · (χ/√k + ρ/(1−ρ) + κ/(1−κ))` with
`ρ = √(χ² + κ²)/(1 − κ)`, is at most `κ`, for every `k ≥ 1`. -/
theorem solution (k : ℕ) (hk : 0 < k) (κ χ : ℝ) (hχ : 0 < χ) (hχκ : χ ≤ κ)
    (hκ : κ ≤ 0.1) :
    closenessBound k κ χ ≤ κ := by
  unfold closenessBound
  have hs : (1:ℝ) ≤ Real.sqrt k := by
    rw [Real.one_le_sqrt]; exact_mod_cast hk
  exact g69a2_cb _ κ χ _ hs hχ hχκ hκ rfl

