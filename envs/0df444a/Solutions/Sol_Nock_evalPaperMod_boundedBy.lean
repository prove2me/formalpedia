-- Prove2me | solution 1 for Nock.evalPaperMod_boundedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:51.117806+00:00
-- url     : https://prove2.me/submissions/bdddeb20-f91a-49ab-8bf6-c593a65464c0

module
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Theorems.Thm_Nock_evalPaperMod_le_evalFBy
public import Theorems.Thm_Nock_FieldEmbedding_evalFBy_boundedBy


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution {q fuel : Nat} {s f r : Noun} (hq : 1 < q)
    (hs : FieldEmbedding.BoundedBy q s) (hf : FieldEmbedding.BoundedBy q f)
    (h : evalPaperMod q fuel s f = some r) : FieldEmbedding.BoundedBy q r :=
  FieldEmbedding.evalFBy_boundedBy hq fuel s f r hs hf (evalPaperMod_le_evalFBy h)
end Nock
