-- Prove2me | solution 2 for Kyprianou.Ch01.beforeStrictUpperCrossingBoundPublic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:34:49.493574+00:00
-- url     : https://prove2.me/submissions/f27ac8a8-aeae-4280-902d-183085ca43d5

import Mathlib.Data.NNReal.Defs
open Set
open scoped NNReal
set_option autoImplicit false

theorem solution (f : ℝ≥0 → ℝ) (x : ℝ)
    (hstart : f 0 ≤ x) (t : ℝ≥0)
    (ht : t < sInf {u : ℝ≥0 | 0 < u ∧ x < f u}) :
    f t ≤ x := by
  by_contra hc
  have hlt : x < f t := not_le.mp hc
  rcases eq_or_lt_of_le (show (0:ℝ≥0) ≤ t from t.2) with h | h
  · rw [← h] at hlt; linarith
  · exact absurd (csInf_le (OrderBot.bddBelow {u : ℝ≥0 | 0 < u ∧ x < f u})
      (show t ∈ {u : ℝ≥0 | 0 < u ∧ x < f u} from ⟨h, hlt⟩)) (not_le.mpr ht)
