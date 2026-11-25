-- Prove2me | solution 1 for NashWilliams.cutF_le_erase_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:16:34.326024+00:00
-- url     : https://prove2.me/submissions/69cb0e15-f51b-4d59-b1d7-189bc10617f7

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution (ends : ι → V × V) (F : Finset ι) (S : Finset V) [DecidableEq ι]
    (i : ι) : cutF ends F S ≤ cutF ends (F.erase i) S + 1 := by
  unfold cutF
  rw [Finset.filter_erase]
  have := Finset.pred_card_le_card_erase
    (s := F.filter fun i => ((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S))
    (a := i)
  omega
end NashWilliams
