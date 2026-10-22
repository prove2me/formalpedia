-- Prove2me | solution 1 for HardyCapset20261020.completion_bound_from_remainder
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T13:33:51.156158+00:00
-- url     : https://prove2.me/submissions/ae819cd8-bfbc-4480-be35-b712c4138808

import Definitions.Def_HardyCapsetModel20261020
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

open scoped BigOperators
set_option maxRecDepth 4096
set_option autoImplicit false
open HardyCapset20261020

theorem solution (A F : Finset Point) (m : ℕ)
    (hF : F ⊆ A) (hcard : F.card + m = 512)
    (hbound : (A \ F).card ≤ m) : A.card ≤ 512 := by
  have h := Finset.card_sdiff_add_card_eq_card hF
  omega
