-- Prove2me | solution 1 for Kirkman.SteinerOp.op_mem_tri
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:50.493667+00:00
-- url     : https://prove2.me/submissions/b4054a25-69ad-4ca1-afe0-7d9b3a524a3f

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
public import Theorems.Thm_Kirkman_SteinerOp_op_op_left
public import Theorems.Thm_Kirkman_SteinerOp_op_op_right
public import Theorems.Thm_P2M_Kirkman_SteinerOp_op_op_right__bbbfe2541011

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
theorem _root_.solution {a b u w : P} (hu : u ∈ S.tri a b) (hw : w ∈ S.tri a b) :
    S.op u w ∈ S.tri a b := by
  unfold tri at *
  simp only [mem_insert, mem_singleton] at hu hw ⊢
  rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
    first
    | simp [S.idem, S.op_op_left, S.op_op_right, S.op_op_right']
    | simp [S.op_op_right, S.comm]
end Kirkman.SteinerOp
