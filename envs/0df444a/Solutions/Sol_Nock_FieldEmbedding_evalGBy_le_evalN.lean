-- Prove2me | solution 1 for Nock.FieldEmbedding.evalGBy_le_evalN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:42.762791+00:00
-- url     : https://prove2.me/submissions/3a60fbad-2c0b-48e1-b1cb-f3029995fe3c

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Theorems.Thm_Nock_FieldEmbedding_agreeBy

set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun
namespace Nock.FieldEmbedding
theorem _root_.solution {q : ℕ} (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : BoundedBy q s) (hf : BoundedBy q f) (h : evalGBy q fuel s f = some r) :
    evalN fuel s f = some r :=
  (agreeBy q hq fuel s f r hs hf h).1
end Nock.FieldEmbedding
