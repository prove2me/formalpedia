-- Prove2me | solution 1 for Nock.Verb.runProgram_output_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:22.812435+00:00
-- url     : https://prove2.me/submissions/fc399f9b-fbb4-478b-ba0a-17ec062bc014

module
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_Determinism
public import Theorems.Thm_Nock_Verb_runProgram_adequate_complete
public import Theorems.Thm_Nock_evalPaper_deterministic


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {s f r₁ r₂ : Noun}
    (h₁ : ∃ fuel, runProgram fuel s f = some r₁)
    (h₂ : ∃ fuel, runProgram fuel s f = some r₂) : r₁ = r₂ := by
  obtain ⟨n₁, hp₁⟩ := (runProgram_adequate_complete s f r₁).1 h₁
  obtain ⟨n₂, hp₂⟩ := (runProgram_adequate_complete s f r₂).1 h₂
  exact evalPaper_deterministic hp₁ hp₂
end Nock.Verb
