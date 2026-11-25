-- Prove2me | solution 1 for MatrixTree.card_ne_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:01:34.784565+00:00
-- url     : https://prove2.me/submissions/c2993c23-b244-42d7-9dd6-0d9cc9902665

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace MatrixTree
theorem _root_.solution [Finite V] (v : V) : Nat.card {u // u ≠ v} + 1 = Nat.card V := by
  classical
  have := Fintype.ofFinite V
  have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  omega
end MatrixTree
