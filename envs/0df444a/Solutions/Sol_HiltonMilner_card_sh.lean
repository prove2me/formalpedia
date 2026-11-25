-- Prove2me | solution 1 for HiltonMilner.card_sh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:49:05.520302+00:00
-- url     : https://prove2.me/submissions/4a2da87c-f627-4fa6-8cc7-5b76f65ddccd

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution (y z : ℕ) (𝒜 : Finset (Finset ℕ)) : #(sh y z 𝒜) = #𝒜 :=
  UV.card_compression _ _ _
end HiltonMilner
