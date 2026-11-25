-- Prove2me | solution 1 for KneserColouring.NoComp.abs_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:10.51009+00:00
-- url     : https://prove2.me/submissions/9e1ffd35-59a5-4dac-8551-08bf7f97c019

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
theorem _root_.solution {S : Finset ℤ} (h : NoComp S) {a b : ℤ} (ha : a ∈ S) (hb : b ∈ S)
    (hab : |a| = |b|) : a = b := by
  rcases abs_eq_abs.1 hab with h' | h'
  · exact h'
  · exact absurd h' (h a ha b hb)
end NoComp
end KneserColouring
