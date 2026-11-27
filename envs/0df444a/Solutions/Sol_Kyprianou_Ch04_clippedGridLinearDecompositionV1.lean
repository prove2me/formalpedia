-- Prove2me | solution 1 for Kyprianou.Ch04.clippedGridLinearDecompositionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:36:32.031956+00:00
-- url     : https://prove2.me/submissions/5ce2efee-4cf3-4a96-b872-7c0873d2f267

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.NNReal.Defs
open scoped NNReal
set_option autoImplicit false

/-- Linearity splits the difference of two clipped state grids into their common
finite-variation grid and their respective compensated small-jump grids. -/
theorem solution (Y Z V H L : NNReal → ℝ) (u : ℕ → NNReal) (n : ℕ) (t : NNReal) :
    let G := fun (X W : NNReal → ℝ) =>
      ∑ k ∈ Finset.range n, W (u k) * (X (min t (u (k+1)))-X (min t (u k)))
    G Y H - G Z L = (G V H - G V L) +
      (G (fun s => Y s-V s) H - G (fun s => Z s-V s) L) := by
  intro G
  have hg (X W : NNReal → ℝ) : G X W = G V W + G (fun s => X s-V s) W := by
    dsimp [G]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hg Y H,hg Z L]
  ring
