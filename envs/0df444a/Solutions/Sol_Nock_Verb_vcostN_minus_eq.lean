-- Prove2me | solution 1 for Nock.Verb.vcostN_minus_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:04.309933+00:00
-- url     : https://prove2.me/submissions/8eb89d9d-bcf9-4537-938b-c2fb0e81edbd

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
    vcostN F (Verb.node .minus l r) = 1 + vcostN F l + vcostN F r := rfl
end Nock.Verb
