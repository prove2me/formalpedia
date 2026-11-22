-- Prove2me | solution 1 for Nock.FieldEmbedding.wut_boundedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:49.408238+00:00
-- url     : https://prove2.me/submissions/6b4b01c3-054c-43b0-a7fd-c7d219e66884

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
theorem _root_.solution {q : ℕ} (hq : 1 < q) (x : Noun) : BoundedBy q (wut x) := by
  cases x with
  | cell _ _ =>
      simp only [wut, BoundedBy_atom]
      omega
  | atom _ => exact hq
end Nock.FieldEmbedding
