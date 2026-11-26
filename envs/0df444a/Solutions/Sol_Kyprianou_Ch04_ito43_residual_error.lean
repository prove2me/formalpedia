-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_residual_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:08:37.912645+00:00
-- url     : https://prove2.me/submissions/14bafc50-b480-4623-a10f-dbb2736cfb94

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_residual_identity
open scoped NNReal
set_option autoImplicit false

/-- A residual stochastic sum has exactly the sum of the time and spatial approximation errors. -/
theorem solution (X g : NNReal → ℝ) (f : ℝ × ℝ → ℝ)
    (T t : NNReal) (ht : t ≤ T) (n : ℕ) (hn : 0 < n) (A B : ℝ) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑ k ∈ Finset.range n, g (u k) * (X (v (k+1)) - X (v k))) -
        (f ((t : ℝ), X t) - f (0, X 0) - A - B) =
      (A - ∑ k ∈ Finset.range n,
        (f ((v (k+1) : ℝ), X (v (k+1))) - f ((v k : ℝ), X (v (k+1))))) +
      (B - ∑ k ∈ Finset.range n, (f ((v k : ℝ), X (v (k+1))) -
        f ((v k : ℝ), X (v k)) - g (u k) * (X (v (k+1)) - X (v k)))) := by
  dsimp
  have H := Kyprianou.Ch04.ito43_grid_residual_identity X g f T t ht n hn
  dsimp at H
  linarith
