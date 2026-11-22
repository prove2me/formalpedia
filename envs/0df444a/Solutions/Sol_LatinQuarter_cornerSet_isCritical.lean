-- Prove2me | solution 1 for LatinQuarter.cornerSet_isCritical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:04.285756+00:00
-- url     : https://prove2.me/submissions/70a38d29-5649-4579-be35-15ef4ec7f5dd

module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Theorems.Thm_LatinQuarter_cornerSet_card
public import Theorems.Thm_LatinQuarter_cornerSet_isDefining
public import Theorems.Thm_LatinQuarter_defining_set_lower_bound


set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    IsCritical (cornerSet n) (cyclic n) := by
  refine ⟨cornerSet_isDefining n hn, ?_⟩
  intro Q hQ hdef
  have hlt := Finset.card_lt_card hQ
  have hlo := defining_set_lower_bound Q (cyclic n) hdef
  rw [cornerSet_card n hn] at hlt
  omega
end LatinQuarter
