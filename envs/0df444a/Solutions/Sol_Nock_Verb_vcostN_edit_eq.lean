-- Prove2me | solution 1 for Nock.Verb.vcostN_edit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:05.02609+00:00
-- url     : https://prove2.me/submissions/90666100-116e-4cf1-9a6c-407c17dc6647

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
    vcostN F (Verb.node .edit l r) = 1 + vcostN F l + vcostN F r := rfl
end Nock.Verb
