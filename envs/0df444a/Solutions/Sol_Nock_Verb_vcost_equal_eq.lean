-- Prove2me | solution 1 for Nock.Verb.vcost_equal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:37.400521+00:00
-- url     : https://prove2.me/submissions/542923fa-6154-40fe-a357-0d08659d2c14

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
    vcost F (Verb.node .equal l r) = 1 + vcost F l + vcost F r := rfl
end Nock.Verb
