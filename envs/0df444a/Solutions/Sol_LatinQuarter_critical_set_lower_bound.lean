-- Prove2me | solution 1 for LatinQuarter.critical_set_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:19.561165+00:00
-- url     : https://prove2.me/submissions/2bd6bea5-56a7-4d00-a0a5-e99fb6502c37

module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Theorems.Thm_LatinQuarter_defining_set_lower_bound


set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsCritical P L) : n * n / 4 ≤ P.card :=
  defining_set_lower_bound P L h.1
end LatinQuarter
