-- Prove2me | solution 1 for NashWilliams.outCutF_erase_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:16:51.873418+00:00
-- url     : https://prove2.me/submissions/e99a50f3-d7a9-47ad-936b-0fcf0f1c4ee1

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
theorem _root_.solution (ends : ι → V × V) (o : ι → Bool) (F : Finset ι) (S : Finset V)
    [DecidableEq ι] (i : ι) : outCutF ends o (F.erase i) S ≤ outCutF ends o F S := by
  unfold outCutF
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
end NashWilliams
