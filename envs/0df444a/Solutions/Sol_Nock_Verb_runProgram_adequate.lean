-- Prove2me | solution 1 for Nock.Verb.runProgram_adequate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:16.659965+00:00
-- url     : https://prove2.me/submissions/0399a5fa-6159-425b-91fd-619f864501bd

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_paperSound_holds

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (hc : PaperComplete) (s f r : Noun) :
    (∃ fuel, runProgram fuel s f = some r) ↔ (∃ fuel, evalPaper fuel s f = some r) :=
  ⟨paperSound_holds s f r, hc s f r⟩
end Nock.Verb
