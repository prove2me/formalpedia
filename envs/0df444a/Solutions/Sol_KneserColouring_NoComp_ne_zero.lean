-- Prove2me | solution 1 for KneserColouring.NoComp.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:13.039049+00:00
-- url     : https://prove2.me/submissions/3a62e941-eb93-479b-818a-8f2176d38f90

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
namespace KneserColouring
namespace NoComp
theorem _root_.solution {S : Finset ℤ} (h : NoComp S) {a : ℤ} (ha : a ∈ S) : a ≠ 0 := by
  intro h0; exact h a ha a ha (by omega)
end NoComp
end KneserColouring
