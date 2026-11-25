-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_discrete_product_summation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:34:00.488069+00:00
-- url     : https://prove2.me/submissions/4c887395-215b-4de4-81c9-dde0496baba5

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
open scoped BigOperators
set_option autoImplicit false

theorem solution (E H : Nat → Real) (n : Nat) :
    (∑ k ∈ Finset.range n, H k * (E (k+1) - E k)) =
      E n * H n - E 0 * H 0 -
        ∑ k ∈ Finset.range n, E (k+1) * (H (k+1) - H k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [ih]
    ring
