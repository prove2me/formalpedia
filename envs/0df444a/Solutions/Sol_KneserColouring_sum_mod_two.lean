-- Prove2me | solution 1 for KneserColouring.sum_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:31.203609+00:00
-- url     : https://prove2.me/submissions/8a0b274d-32fd-461c-be3b-ca57d9b4def5

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ x ∈ s, f x) % 2 = (s.filter (fun x => f x % 2 = 1)).card % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (fun h' => ha (mem_filter.1 h').1)]
      omega
    · omega
end KneserColouring
