-- Prove2me | solution 1 for Nock.Verb.vcostN_null_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:07.003568+00:00
-- url     : https://prove2.me/submissions/04418537-90e2-4bcb-8f8e-72e2f229b775

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
    vcostN F (Verb.node .null l r) = vcostN F l + vcostN F r := by
  simp only [vcostN]; omega
end Nock.Verb
