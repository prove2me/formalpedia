-- Prove2me | solution 1 for HiltonMilner.card_shiftSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:06:00.141474+00:00
-- url     : https://prove2.me/submissions/944e6a79-802c-455f-9414-75b4dbc71646

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution (y z : ℕ) (A : Finset ℕ) : #(shiftSet y z A) = #A := by
  unfold shiftSet
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => h.1 (mem_of_mem_erase h')), card_erase_of_mem h.2]
    have : 0 < #A := card_pos.2 ⟨z, h.2⟩
    omega
  · rfl
end HiltonMilner
