-- Prove2me | solution 1 for Nock.paper_field_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:28.635277+00:00
-- url     : https://prove2.me/submissions/b3f92506-6f80-493c-83c1-c836686e3e22

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
public import Theorems.Thm_Nock_evalGPaper_le_evalGBy
public import Theorems.Thm_Nock_evalGPaper_le_evalPaper
public import Theorems.Thm_Nock_evalGPaper_le_evalPaperMod
public import Theorems.Thm_Nock_FieldEmbedding_agreeBy
public import Theorems.Thm_Nock_Verb_runProgram_adequate_complete
public import Theorems.Thm_Nock_evalPaperMod_le_evalFBy
public import Theorems.Thm_Nock_evalPaper_le_evalN


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution (q : Nat) (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : FieldEmbedding.BoundedBy q s) (hf : FieldEmbedding.BoundedBy q f)
    (hG : evalGPaper q fuel s f = some r) :
    (∃ n, Verb.runProgram n s f = some r) ∧
      evalPaper fuel s f = some r ∧
      evalPaperMod q fuel s f = some r ∧
      FieldEmbedding.evalFBy q fuel s f = some r ∧
      evalN fuel s f = some r ∧
      FieldEmbedding.BoundedBy q r := by
  have hP : evalPaper fuel s f = some r := evalGPaper_le_evalPaper hG
  have hM : evalPaperMod q fuel s f = some r := evalGPaper_le_evalPaperMod hG
  have hB : FieldEmbedding.BoundedBy q r :=
    (FieldEmbedding.agreeBy q hq fuel s f r hs hf (evalGPaper_le_evalGBy hG)).2.2
  exact ⟨(Verb.runProgram_adequate_complete s f r).2 ⟨fuel, hP⟩, hP, hM,
    evalPaperMod_le_evalFBy hM, evalPaper_le_evalN hP, hB⟩
end Nock
