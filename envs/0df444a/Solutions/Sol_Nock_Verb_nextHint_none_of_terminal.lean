-- Prove2me | solution 1 for Nock.Verb.nextHint_none_of_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:52.533981+00:00
-- url     : https://prove2.me/submissions/9eaeb1a7-3f9f-494d-b438-ccd3ee888859

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_getIndex_none_of_terminal


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} (h : isTerminal v = true) : nextHint v = none := by
  unfold nextHint; rw [getIndex_none_of_terminal h]
end Nock.Verb
