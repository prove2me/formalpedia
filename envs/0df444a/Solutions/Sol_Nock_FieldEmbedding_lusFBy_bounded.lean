-- Prove2me | solution 1 for Nock.FieldEmbedding.lusFBy_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:49.530993+00:00
-- url     : https://prove2.me/submissions/b55d206b-e301-4b68-8aa3-b1fdf0b4d661

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_atom
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_cell
attribute [local simp] Nock.FieldEmbedding.BoundedBy_atom
attribute [local simp] Nock.FieldEmbedding.BoundedBy_cell

set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun
namespace Nock.FieldEmbedding
theorem _root_.solution {q : ℕ} (hq : 0 < q) {x m : Noun}
    (h : lusFBy q x = some m) : BoundedBy q m := by
  cases x with
  | atom n => simp only [lusFBy] at h; obtain rfl := Option.some.inj h; exact Nat.mod_lt _ hq
  | cell l r => simp [lusFBy] at h
end Nock.FieldEmbedding
