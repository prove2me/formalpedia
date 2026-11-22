-- Prove2me | solution 1 for Nock.FieldEmbedding.BoundedBy_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:57.204831+00:00
-- url     : https://prove2.me/submissions/23248d6d-bc81-453b-992a-47c241cb9b05

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
theorem _root_.solution {q : ℕ} {l r : Noun} :
    BoundedBy q (.cell l r) ↔ BoundedBy q l ∧ BoundedBy q r := Iff.rfl
end Nock.FieldEmbedding
