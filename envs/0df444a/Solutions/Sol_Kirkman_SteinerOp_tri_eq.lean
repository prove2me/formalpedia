-- Prove2me | solution 1 for Kirkman.SteinerOp.tri_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:47:02.994063+00:00
-- url     : https://prove2.me/submissions/b59da2a1-4a3f-4781-867f-4581f1523a63

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
public import Theorems.Thm_Kirkman_SteinerOp_card_tri
public import Theorems.Thm_Kirkman_SteinerOp_op_mem_tri

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
theorem _root_.solution {a b x y : P} (hab : a ≠ b) (hxy : x ≠ y) (hx : x ∈ S.tri a b)
    (hy : y ∈ S.tri a b) : S.tri a b = S.tri x y := by
  symm
  refine eq_of_subset_of_card_le ?_ (by rw [S.card_tri hab, S.card_tri hxy])
  intro w hw
  unfold tri at hw
  simp only [mem_insert, mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact S.op_mem_tri hx hy
end Kirkman.SteinerOp
