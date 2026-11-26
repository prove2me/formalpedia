-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_grid_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:46:14.015022+00:00
-- url     : https://prove2.me/submissions/187a1b58-ca68-4b4f-9fd3-36915759dbae

import Mathlib
open scoped NNReal
set_option autoImplicit false

/-- Exact stopped-grid time/space decomposition of a two-variable increment. -/
theorem solution (X : NNReal → ℝ) (f : ℝ × ℝ → ℝ)
    (u : ℕ → NNReal) (n : ℕ) (t : NNReal) :
    f ((min t (u n) : NNReal), X (min t (u n))) -
      f ((min t (u 0) : NNReal), X (min t (u 0))) =
      (∑ k ∈ Finset.range n,
        (f ((min t (u (k+1)) : NNReal), X (min t (u (k+1)))) -
          f ((min t (u k) : NNReal), X (min t (u (k+1)))))) +
      (∑ k ∈ Finset.range n,
        (f ((min t (u k) : NNReal), X (min t (u (k+1)))) -
          f ((min t (u k) : NNReal), X (min t (u k))))) := by
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ k ∈ Finset.range n,
        (f ((min t (u (k+1)) : NNReal), X (min t (u (k+1)))) -
          f ((min t (u k) : NNReal), X (min t (u k)))) :=
      (Finset.sum_range_sub (fun k => f ((min t (u k) : NNReal), X (min t (u k)))) n).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
