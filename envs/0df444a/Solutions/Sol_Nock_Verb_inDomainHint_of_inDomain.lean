-- Prove2me | solution 1 for Nock.Verb.inDomainHint_of_inDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:45.955833+00:00
-- url     : https://prove2.me/submissions/a90ea21b-e8ed-46ab-b446-da7c9d8fe400

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} (h : inDomain v = true) : inDomainHint v = true := by
  simp only [inDomainHint, h, Bool.true_or]
end Nock.Verb
