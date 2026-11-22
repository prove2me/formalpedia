-- Prove2me | solution 1 for Nock.runProgram_of_evalGPaper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:54.567009+00:00
-- url     : https://prove2.me/submissions/56f3cd69-9936-4cd5-ab69-560b45f8213a

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
public import Theorems.Thm_Nock_evalGPaper_le_evalPaper
public import Theorems.Thm_Nock_Verb_runProgram_adequate_complete


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution {q fuel : Nat} {s f r : Noun}
    (hG : evalGPaper q fuel s f = some r) : ∃ n, Verb.runProgram n s f = some r :=
  (Verb.runProgram_adequate_complete s f r).2 ⟨fuel, evalGPaper_le_evalPaper hG⟩
end Nock
