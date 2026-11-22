-- Prove2me | solution 1 for Nock.Verb.vcostN_slot_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:59.518278+00:00
-- url     : https://prove2.me/submissions/54c6be4a-ccd6-4967-b143-e25d4fda0aa6

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
theorem _root_.solution {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .slot l r) = 1 + vcostN F l + vcostN F r := rfl
end Nock.Verb
