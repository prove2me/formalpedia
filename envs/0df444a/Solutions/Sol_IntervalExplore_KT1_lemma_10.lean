-- Prove2me | solution 1 for IntervalExplore.KT1.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-12T13:23:53.846127+00:00
-- url     : https://prove2.me/submissions/7ef822f1-047d-4566-9bf4-8f1a646e2eff

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false

private lemma exp_gt_twice (y : ℝ) (hy : 0 < y) : 2 * y < Real.exp y := by
  have h := Real.add_one_lt_exp (ne_of_gt (show 0 < y / 2 by positivity))
  have he : 0 < Real.exp (y / 2) := Real.exp_pos _
  have hs : 0 ≤ (y / 2 - 1) ^ 2 := sq_nonneg _
  have hsq : (y / 2 + 1) ^ 2 < (Real.exp (y / 2)) ^ 2 := by nlinarith
  have heq : Real.exp y = (Real.exp (y / 2)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  nlinarith

theorem solution (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 3 ≤ n) :
    Real.log n < x * (n : ℝ) ^ (1 / (2 * x)) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have h := exp_gt_twice (Real.log n / (2 * x)) (by positivity)
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < n)]
  have hr : Real.log (n : ℝ) * (1 / (2 * x)) = Real.log n / (2 * x) := by ring
  rw [hr]
  have hmul := mul_lt_mul_of_pos_left h hx
  have heq : x * (2 * (Real.log (n : ℝ) / (2 * x))) = Real.log n := by
    field_simp
  rwa [heq] at hmul

#print axioms solution