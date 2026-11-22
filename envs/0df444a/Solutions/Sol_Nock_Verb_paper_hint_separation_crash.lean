-- Prove2me | solution 1 for Nock.Verb.paper_hint_separation_crash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:15.070685+00:00
-- url     : https://prove2.me/submissions/8f6a5ef4-182c-4ccb-94d7-a52561d36c0d

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_runHint_hintStatic
public import Theorems.Thm_Nock_Verb_evalProgram_hint_crash

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution :
    evalProgram 1 (Noun.atom 42) hintProgStatic = .crash
    ∧ (∃ fuel, runHintProgram fuel (Noun.atom 42) hintProgStatic = some (Noun.atom 42)) :=
  ⟨evalProgram_hint_crash _ _, 32, runHint_hintStatic⟩
end Nock.Verb
