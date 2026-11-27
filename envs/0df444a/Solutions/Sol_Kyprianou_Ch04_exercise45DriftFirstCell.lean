-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45DriftFirstCell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:58:33.87508+00:00
-- url     : https://prove2.me/submissions/fec1bbd0-1c3b-42c6-a7c8-9d8bfb41d112

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2

open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- At the end of the first cell of the unit grid, only its weight contributes. -/
theorem solution (n : ℕ) (hn : 0 < n) (a : ℝ) :
    (∑ k ∈ Finset.range n,
      let u : NNReal := (1 : NNReal) * (k : NNReal) / (n : NNReal)
      let v : NNReal := (1 : NNReal) * ((k + 1 : ℕ) : NNReal) / (n : NNReal)
      (2 * (if u = 0 then a else (u : ℝ))) *
        (((min (1 / (n : NNReal)) v : NNReal) : ℝ) -
          ((min (1 / (n : NNReal)) u : NNReal) : ℝ))) =
        2 * a / (n : ℝ) := by
  classical
  rw [Finset.sum_eq_single 0]
  · simp [div_eq_mul_inv]
  · intro k _ hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hu : (1 : NNReal) / (n : NNReal) ≤
        (1 : NNReal) * (k : NNReal) / (n : NNReal) := by
      rw [one_mul]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hk1) (by positivity)
    have hv : (1 : NNReal) / (n : NNReal) ≤
        (1 : NNReal) * ((k+1 : ℕ) : NNReal) / (n : NNReal) := by
      rw [one_mul]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.succ_pos k)) (by positivity)
    simp only [min_eq_left hu, min_eq_left hv, sub_self, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr hn)).elim
