-- Prove2me | solution 1 for LatinQuarter.quarter_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:49.7253+00:00
-- url     : https://prove2.me/submissions/5c148e09-066d-4d42-9802-aaed444f3cf4

module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Theorems.Thm_LatinQuarter_cornerSet_card
public import Theorems.Thm_LatinQuarter_cornerSet_isCritical
public import Theorems.Thm_LatinQuarter_defining_set_lower_bound


set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    (∀ (L : Square n) (P : Finset (Cell n)),
      IsDefining P L → n * n / 4 ≤ P.card) ∧
    IsCritical (cornerSet n) (cyclic n) ∧
    (cornerSet n).card = n * n / 4 :=
  ⟨fun L P h => defining_set_lower_bound P L h,
    cornerSet_isCritical n hn, cornerSet_card n hn⟩
end LatinQuarter
