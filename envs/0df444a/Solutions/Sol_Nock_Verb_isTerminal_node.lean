-- Prove2me | solution 1 for Nock.Verb.isTerminal_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:26.608803+00:00
-- url     : https://prove2.me/submissions/77438a8f-d3a8-4580-866d-b30f61643997

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a : Action} {l r : Verb} :
    isTerminal (Verb.node a l r) = (a.isNull && isTerminal l && isTerminal r) := rfl
end Nock.Verb
