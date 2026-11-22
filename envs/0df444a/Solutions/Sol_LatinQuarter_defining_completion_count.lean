-- Prove2me | solution 1 for LatinQuarter.defining_completion_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:04.922027+00:00
-- url     : https://prove2.me/submissions/d233dcfe-11b0-461a-844d-7b572d97363e

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Theorems.Thm_LatinQuarter_defining_iff_completions_eq_singleton

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution {n : ℕ} {P : Finset (Cell n)}
    {L : Square n} (h : IsDefining P L) :
    (completions P L).card = 1 := by
  rw [(defining_iff_completions_eq_singleton P L).mp h]
  exact Finset.card_singleton L
end LatinQuarter
