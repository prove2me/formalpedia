-- Prove2me | solution 1 for KneserColouring.isAlt_zero_one_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:22.047728+00:00
-- url     : https://prove2.me/submissions/fc13161a-bfba-4744-93da-10c3047e681c

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
namespace KneserColouring
theorem _root_.solution {S : Finset ℤ} (hS : S.Nonempty) (h0 : IsAlt 0 S)
    (h1 : IsAlt 1 S) : False := by
  obtain ⟨a, ha⟩ := hS
  have := (h0 a ha).symm.trans (h1 a ha)
  rw [Nat.add_zero, Nat.even_add_one] at this
  tauto
end KneserColouring
