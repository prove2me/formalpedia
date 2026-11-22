-- Prove2me | solution 1 for LatinQuarter.cornerSet_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:19.141067+00:00
-- url     : https://prove2.me/submissions/6b4b8320-99b5-4036-b22a-609d8d66f56d

module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Theorems.Thm_LatinQuarter_cornerSet_card_le
public import Theorems.Thm_LatinQuarter_cornerSet_isDefining
public import Theorems.Thm_LatinQuarter_defining_set_lower_bound


set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    (cornerSet n).card = n * n / 4 := by
  apply le_antisymm (cornerSet_card_le n)
  exact defining_set_lower_bound _ _ (cornerSet_isDefining n hn)
end LatinQuarter
