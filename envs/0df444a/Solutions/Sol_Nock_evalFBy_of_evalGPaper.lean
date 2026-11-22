-- Prove2me | solution 1 for Nock.evalFBy_of_evalGPaper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:57.403563+00:00
-- url     : https://prove2.me/submissions/e066f26c-26b5-4434-bf36-57b11d000b8b

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
public import Theorems.Thm_Nock_evalGPaper_le_evalPaperMod
public import Theorems.Thm_Nock_evalPaperMod_le_evalFBy


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution {q fuel : Nat} {s f r : Noun}
    (hG : evalGPaper q fuel s f = some r) :
    FieldEmbedding.evalFBy q fuel s f = some r :=
  evalPaperMod_le_evalFBy (evalGPaper_le_evalPaperMod hG)
end Nock
