-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_grid_residual_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:48:30.352814+00:00
-- url     : https://prove2.me/submissions/35407235-7599-45d2-852c-a0a91ebb5e2c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_telescope
open scoped NNReal
set_option autoImplicit false

/-- The stopped-grid stochastic sum equals the total increment less the time and spatial remainders. -/
theorem solution (X g : NNReal → ℝ) (f : ℝ × ℝ → ℝ)
    (T t : NNReal) (ht : t ≤ T) (n : ℕ) (hn : 0 < n) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑ k ∈ Finset.range n, g (u k) * (X (v (k+1)) - X (v k))) =
      f ((t : ℝ), X t) - f (0, X 0) -
      (∑ k ∈ Finset.range n, (f ((v (k+1) : ℝ), X (v (k+1))) -
        f ((v k : ℝ), X (v (k+1))))) -
      (∑ k ∈ Finset.range n, (f ((v k : ℝ), X (v (k+1))) -
        f ((v k : ℝ), X (v k)) - g (u k) * (X (v (k+1)) - X (v k)))) := by
  intro u v
  have h0 : u 0 = 0 := by simp [u]
  have hn0 : (n : NNReal) ≠ 0 := by exact_mod_cast hn.ne'
  have hN : u n = T := by simp [u, mul_div_cancel_right₀ _ hn0]
  have H := Kyprianou.Ch04.ito43_grid_telescope X f u n t
  rw [hN, min_eq_left ht, h0, min_eq_right zero_le] at H
  change f ((t : ℝ), X t) - f (0, X 0) = _ at H
  have hR : (∑ k ∈ Finset.range n, (f ((v k : ℝ), X (v (k+1))) -
        f ((v k : ℝ), X (v k)) - g (u k) * (X (v (k+1)) - X (v k)))) =
      (∑ k ∈ Finset.range n, (f ((v k : ℝ), X (v (k+1))) -
        f ((v k : ℝ), X (v k)))) -
      (∑ k ∈ Finset.range n, g (u k) * (X (v (k+1)) - X (v k))) :=
    Finset.sum_sub_distrib _ _
  rw [hR]
  change f ((t : ℝ), X t) - f (0, X 0) =
    (∑ k ∈ Finset.range n, (f ((v (k+1) : ℝ), X (v (k+1))) -
      f ((v k : ℝ), X (v (k+1))))) +
    (∑ k ∈ Finset.range n, (f ((v k : ℝ), X (v (k+1))) -
      f ((v k : ℝ), X (v k)))) at H
  linarith
