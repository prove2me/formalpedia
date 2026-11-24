-- Prove2me | solution 1 for Kirkman.SteinerOp.mem_tri_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:41:24.480449+00:00
-- url     : https://prove2.me/submissions/34b5b586-9c26-4745-843a-ecc6f0ed08fa

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
theorem _root_.solution (x y : P) : y ∈ S.tri x y := by unfold tri; simp
end Kirkman.SteinerOp
