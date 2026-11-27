-- Prove2me | solution 1 for Kyprianou.Ch04.clippedGridZeroCellV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:56:55.138121+00:00
-- url     : https://prove2.me/submissions/37869deb-06d2-4152-8804-8ddcf52fb33d

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic
open MeasureTheory Filter Set Topology
open scoped NNReal Classical
set_option autoImplicit false

theorem solution
    (Y H : NNReal → ℝ) (u : ℕ → NNReal) (n : ℕ) (t : NNReal)
    (hn : 0 < n) (h0 : u 0 = 0)
    (hp : ∀ k ∈ Finset.range n, k ≠ 0 → 0 < u k) :
    (∑ k ∈ Finset.range n, H (u k) * (Y (min t (u (k+1))) - Y (min t (u k)))) -
      (∑ k ∈ Finset.range n, (if u k = 0 then 0 else H (u k)) *
        (Y (min t (u (k+1))) - Y (min t (u k)))) =
      H 0 * (Y (min t (u 1)) - Y 0) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single 0]
  · simp [h0]
  · intro k hk hk0
    simp [ne_of_gt (hp k hk hk0)]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hn))
