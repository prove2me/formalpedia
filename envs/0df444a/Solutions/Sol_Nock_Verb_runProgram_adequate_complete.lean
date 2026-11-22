-- Prove2me | solution 1 for Nock.Verb.runProgram_adequate_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:39.263622+00:00
-- url     : https://prove2.me/submissions/82fe48b2-4c42-431d-842c-cbeabd581eef

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_paperComplete_holds
public import Theorems.Thm_Nock_Verb_runProgram_adequate


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (s f r : Noun) :
    (∃ fuel, runProgram fuel s f = some r) ↔ (∃ fuel, evalPaper fuel s f = some r) :=
  runProgram_adequate paperComplete_holds s f r
end Nock.Verb
