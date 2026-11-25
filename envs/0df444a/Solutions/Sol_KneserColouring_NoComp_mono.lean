-- Prove2me | solution 1 for KneserColouring.NoComp.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:59.27598+00:00
-- url     : https://prove2.me/submissions/d4c7720d-64d7-4e0d-afa6-0056763609c2

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
theorem _root_.solution {S T : Finset ℤ} (h : NoComp S) (hT : T ⊆ S) : NoComp T :=
  fun a ha b hb => h a (hT ha) b (hT hb)
end NoComp
end KneserColouring
