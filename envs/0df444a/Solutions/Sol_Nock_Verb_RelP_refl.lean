-- Prove2me | solution 1 for Nock.Verb.RelP.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:59.415769+00:00
-- url     : https://prove2.me/submissions/104893d7-eb1a-4eab-94f5-f9e6a1b1caaa

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
namespace RelP
theorem _root_.solution : ∀ v, RelP v v
  | .leaf _   => .leaf
  | .node _ l r => .cong (solution l) (solution r)
end RelP
end Nock.Verb
