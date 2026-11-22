-- Prove2me | solution 1 for Nock.Verb.vcost_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:07.637227+00:00
-- url     : https://prove2.me/submissions/bc60ea26-844e-4b51-a9e8-f76b93760cfc

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
theorem _root_.solution {F : Nat} {l r : Verb} : vcost F (Verb.node .star l r) =
    (match denP F l, denP F r with | some sa, some fo => pcost F sa fo | _, _ => 0)
      + vcost F l + vcost F r := rfl
end Nock.Verb
