-- Prove2me | solution 1 for Nock.Verb.vcost_wut_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:55.828405+00:00
-- url     : https://prove2.me/submissions/135765a9-042c-41f0-9a77-b81a66f81f56

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
    vcost F (Verb.node .wut l r) = vcost F l + vcost F r := by
  simp only [vcost]; omega
end Nock.Verb
