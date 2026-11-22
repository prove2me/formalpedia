-- Prove2me | solution 1 for Nock.FieldEmbedding.noOverflow_agreeBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:43.143488+00:00
-- url     : https://prove2.me/submissions/428cfd67-cabd-4575-84b4-6c1506fdc252

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
    (hs : BoundedBy q s) (hf : BoundedBy q f) (hno : evalGBy q fuel s f = some r) :
    evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧ BoundedBy q r :=
  agreeBy q hq fuel s f r hs hf hno
end Nock.FieldEmbedding
