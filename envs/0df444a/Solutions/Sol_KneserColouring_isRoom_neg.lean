-- Prove2me | solution 1 for KneserColouring.isRoom_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:14.249637+00:00
-- url     : https://prove2.me/submissions/f33fe7ec-1fb4-4773-9db6-288f4a01b5b8

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
public import Theorems.Thm_KneserColouring_signType_neg_ne_zero


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution {k : ℕ} {t : Fin n → SignType} {ρ : Equiv.Perm (Fin n)} :
    IsRoom k (-t, ρ) ↔ IsRoom k (t, ρ) := by
  unfold IsRoom
  simp only [Pi.neg_apply, signType_neg_ne_zero]
end KneserColouring
