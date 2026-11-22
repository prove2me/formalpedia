-- Prove2me | solution 1 for Nock.FieldEmbedding.tis_boundedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:51.071947+00:00
-- url     : https://prove2.me/submissions/1174f938-b6f4-491d-8af9-c5802db9af70

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
theorem _root_.solution {q : ℕ} (hq : 1 < q) (a b : Noun) : BoundedBy q (tis a b) := by
  unfold tis; split
  · simp only [BoundedBy_atom]
    omega
  · exact hq
end Nock.FieldEmbedding
