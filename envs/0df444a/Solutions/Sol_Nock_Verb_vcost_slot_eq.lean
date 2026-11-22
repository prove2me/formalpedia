-- Prove2me | solution 1 for Nock.Verb.vcost_slot_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:36.839797+00:00
-- url     : https://prove2.me/submissions/66ce45d0-b38d-4b5e-81cc-4ac741615b51

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
theorem _root_.solution {F : Nat} {l r : Verb} :
    vcost F (Verb.node .slot l r) = 1 + vcost F l + vcost F r := rfl
end Nock.Verb
