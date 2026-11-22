-- Prove2me | solution 1 for Nock.Verb.runHint_adequate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:39.370806+00:00
-- url     : https://prove2.me/submissions/051e0ef6-bd20-4433-8e29-0da875cdddc2

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_runHintProgram_sound

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (hc : HintComplete) (s f r : Noun) :
    (∃ fuel, runHintProgram fuel s f = some r) ↔ (∃ fuel, evalN fuel s f = some r) :=
  ⟨fun ⟨_, h⟩ => runHintProgram_sound h, hc s f r⟩
end Nock.Verb
