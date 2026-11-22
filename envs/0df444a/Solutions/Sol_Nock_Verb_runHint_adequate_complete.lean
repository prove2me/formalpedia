-- Prove2me | solution 1 for Nock.Verb.runHint_adequate_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:31.823388+00:00
-- url     : https://prove2.me/submissions/706479cc-84e8-47c1-929b-82946d9036c7

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_hintComplete_holds
public import Theorems.Thm_Nock_Verb_runHint_adequate


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (s f r : Noun) :
    (∃ fuel, runHintProgram fuel s f = some r) ↔ (∃ fuel, evalN fuel s f = some r) :=
  runHint_adequate hintComplete_holds s f r
end Nock.Verb
