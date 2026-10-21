-- Prove2me | solution 1 for HiddenRebate.Fixed.selStar_cost_coords
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:51:23.963171+00:00
-- url     : https://prove2.me/submissions/f00a0209-e578-47de-83f3-ffd34209e875

import Mathlib
import Definitions.Def_HiddenRebate_Fixed_Model

open HiddenRebate.Fixed

theorem solution (r : ℝ) (x : ℝ × ℝ) :
    (contractStar r).1 (quote r x) = Supplier.S ↔ x.1 ≤ x.2 := by
  simp only [contractStar, selStar, quote, add_sub_cancel_right]
  split_ifs with h <;> simp [h]
