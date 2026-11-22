-- Prove2me | solution 1 for Nock.Verb.denP_terminal_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:42.280679+00:00
-- url     : https://prove2.me/submissions/fe77cb87-3201-4c4b-a41b-5de4b4113229

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_DenP_terminal_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {F : Nat} {y : Noun}
    (ht : isTerminal v = true) (h : denP F v = some y) : y = v.noun :=
  (DenP_terminal_iff ht).1 ⟨F, h⟩
end Nock.Verb
