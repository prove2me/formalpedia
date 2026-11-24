-- Prove2me | solution 1 for Kirkman.SteinerOp.mem_tri_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:27.715816+00:00
-- url     : https://prove2.me/submissions/d1ea8389-48c5-4b26-88ec-2d20b6ec0910

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
variable [DecidableEq P]
namespace Kirkman.SteinerOp
theorem _root_.solution (x y : P) : x ∈ S.tri x y := by unfold tri; simp
end Kirkman.SteinerOp
