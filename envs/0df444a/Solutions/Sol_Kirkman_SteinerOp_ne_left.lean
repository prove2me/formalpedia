-- Prove2me | solution 1 for Kirkman.SteinerOp.ne_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:24.325869+00:00
-- url     : https://prove2.me/submissions/03cb7ee9-ca70-4182-827a-f4877fa8fdf4

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
variable {P : Type*}
open Kirkman.SteinerOp
variable (S : SteinerOp P)
namespace Kirkman.SteinerOp
theorem _root_.solution {x y : P} (h : x ≠ y) : S.op x y ≠ x := by
  intro e
  apply h
  have := S.cancel x y
  rwa [e, S.idem] at this
end Kirkman.SteinerOp
