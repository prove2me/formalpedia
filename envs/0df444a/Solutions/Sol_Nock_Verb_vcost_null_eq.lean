-- Prove2me | solution 1 for Nock.Verb.vcost_null_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:43.855334+00:00
-- url     : https://prove2.me/submissions/8a083c7f-42fb-437e-8e86-e1bf349fd837

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
    vcost F (Verb.node .null l r) = vcost F l + vcost F r := by
  simp only [vcost]; omega
end Nock.Verb
