-- Prove2me | solution 1 for HardyCapset20261020.integer_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T13:33:49.722989+00:00
-- url     : https://prove2.me/submissions/07f829b4-c965-41e4-be10-ffd8960726e6

import Definitions.Def_HardyCapsetModel20261020
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

open scoped BigOperators
set_option maxRecDepth 4096
set_option autoImplicit false
open HardyCapset20261020

theorem solution (k m : ℕ) (cost : ℚ)
    (hk : (k : ℚ) ≤ cost) (hc : cost < (m : ℚ) + 1) : k ≤ m := by
  have h : (k : ℚ) < (m : ℚ) + 1 := lt_of_le_of_lt hk hc
  have hnat : k < m + 1 := by exact_mod_cast h
  omega
