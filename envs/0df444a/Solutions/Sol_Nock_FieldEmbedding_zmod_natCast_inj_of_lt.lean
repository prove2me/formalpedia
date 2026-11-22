-- Prove2me | solution 1 for Nock.FieldEmbedding.zmod_natCast_inj_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:56.723945+00:00
-- url     : https://prove2.me/submissions/57837dc5-78e7-47e7-8588-ac0579998361

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
theorem _root_.solution {q m n : ℕ} (hm : m < q) (hn : n < q)
    (h : (m : ZMod q) = (n : ZMod q)) : m = n := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hn] at this
end Nock.FieldEmbedding
