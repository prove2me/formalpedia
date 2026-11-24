-- Prove2me | solution 1 for Kirkman.SteinerOp.op_op_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:27.160952+00:00
-- url     : https://prove2.me/submissions/d20621fc-3d6c-4dec-a196-ca5822622b48

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
theorem _root_.solution (x y : P) : S.op (S.op x y) x = y := by rw [S.comm, S.cancel]
end Kirkman.SteinerOp
