-- Prove2me | solution 1 for Nock.FieldEmbedding.BoundedBy_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:56.721843+00:00
-- url     : https://prove2.me/submissions/736a9c74-6917-4816-994c-369993799119

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval

set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun
namespace Nock.FieldEmbedding
theorem _root_.solution {q n : ℕ} : BoundedBy q (.atom n) ↔ n < q := Iff.rfl
end Nock.FieldEmbedding
