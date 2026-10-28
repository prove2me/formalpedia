-- Prove2me | solution 1 for LL_Decomp1528a.log_le_log_floor_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:27:27.52625+00:00
-- url     : https://prove2.me/submissions/5942f325-8d91-48d4-ac25-0141512d3fca

import Mathlib

open Real

theorem solution {x : ℝ} (hx : 5 ≤ x) : log x ≤ log (⌊x⌋₊ : ℝ) + 0.2 := by
  have hf5 : (5:ℝ) ≤ ⌊x⌋₊ := by
    have : 5 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  have hfpos : (0:ℝ) < ⌊x⌋₊ := by linarith
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have h := Real.log_le_sub_one_of_pos (x := x / ⌊x⌋₊) (by positivity)
  rw [Real.log_div (by linarith) hfpos.ne'] at h
  have : x / ⌊x⌋₊ - 1 ≤ 0.2 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hfpos]; nlinarith
  linarith
