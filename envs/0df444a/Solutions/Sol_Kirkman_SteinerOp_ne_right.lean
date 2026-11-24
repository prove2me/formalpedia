-- Prove2me | solution 1 for Kirkman.SteinerOp.ne_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:42:57.033839+00:00
-- url     : https://prove2.me/submissions/e5550413-dd59-4f83-b277-a268e9a6dc8f

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
public import Theorems.Thm_Kirkman_SteinerOp_ne_left

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
variable {P : Type*}
open Kirkman.SteinerOp
variable (S : SteinerOp P)
namespace Kirkman.SteinerOp
theorem _root_.solution {x y : P} (h : x ≠ y) : S.op x y ≠ y := by
  rw [S.comm]; exact S.ne_left (Ne.symm h)
end Kirkman.SteinerOp
