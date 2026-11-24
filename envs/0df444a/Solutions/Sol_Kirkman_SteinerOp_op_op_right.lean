-- Prove2me | solution 1 for Kirkman.SteinerOp.op_op_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:26.612325+00:00
-- url     : https://prove2.me/submissions/3f6e86ab-cf5f-45c0-8702-8babf448dd66

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
omit [DecidableEq P]
namespace Kirkman.SteinerOp
theorem _root_.solution (x y : P) : S.op y (S.op x y) = x := by rw [S.comm x y, S.cancel]
end Kirkman.SteinerOp
