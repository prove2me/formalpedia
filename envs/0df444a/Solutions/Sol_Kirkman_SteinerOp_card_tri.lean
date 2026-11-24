-- Prove2me | solution 1 for Kirkman.SteinerOp.card_tri
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:37.42954+00:00
-- url     : https://prove2.me/submissions/0a1cc29e-e280-44c3-8c72-aca55b6aa1c2

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
public import Theorems.Thm_Kirkman_SteinerOp_ne_left
public import Theorems.Thm_Kirkman_SteinerOp_ne_right

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
theorem _root_.solution {x y : P} (h : x ≠ y) : #(S.tri x y) = 3 := by
  unfold tri
  rw [card_insert_of_notMem, card_pair (S.ne_right h).symm]
  simp only [mem_insert, mem_singleton, not_or]
  exact ⟨h, (S.ne_left h).symm⟩
end Kirkman.SteinerOp
