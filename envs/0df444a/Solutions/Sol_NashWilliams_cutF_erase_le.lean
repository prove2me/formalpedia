-- Prove2me | solution 1 for NashWilliams.cutF_erase_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:17.752235+00:00
-- url     : https://prove2.me/submissions/bf577fee-ad07-45d3-975c-c34ba59379d7

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
theorem _root_.solution (ends : ι → V × V) (F : Finset ι) (S : Finset V) [DecidableEq ι] (i : ι) :
    cutF ends (F.erase i) S ≤ cutF ends F S := by
  unfold cutF
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
end NashWilliams
