-- Prove2me | solution 1 for KneserColouring.even_card_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:11.414587+00:00
-- url     : https://prove2.me/submissions/fcc4aef5-45af-4fff-811d-e76555bcb6d9

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
namespace KneserColouring
theorem _root_.solution {α : Type*} (s : Finset α) (g : α → α)
    (hg_mem : ∀ a ∈ s, g a ∈ s) (hne : ∀ a ∈ s, g a ≠ a) (hinv : ∀ a ∈ s, g (g a) = a) :
    Even s.card := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  have : ∑ _x ∈ s, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => g a) (fun _ _ => by decide)
      (fun a ha _ => hne a ha) (fun a ha => hg_mem a ha) (fun a ha => hinv a ha)
  simpa using this
end KneserColouring
