-- Prove2me | solution 1 for Nock.Verb.runHintProgram_output_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:25.812813+00:00
-- url     : https://prove2.me/submissions/f2d0d565-a51e-4145-a22e-2c3975e173cd

module
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_Determinism
public import Theorems.Thm_Nock_Verb_runHint_adequate_complete
public import Theorems.Thm_Nock_evalN_deterministic


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {s f r₁ r₂ : Noun}
    (h₁ : ∃ fuel, runHintProgram fuel s f = some r₁)
    (h₂ : ∃ fuel, runHintProgram fuel s f = some r₂) : r₁ = r₂ := by
  obtain ⟨n₁, hp₁⟩ := (runHint_adequate_complete s f r₁).1 h₁
  obtain ⟨n₂, hp₂⟩ := (runHint_adequate_complete s f r₂).1 h₂
  exact evalN_deterministic hp₁ hp₂
end Nock.Verb
