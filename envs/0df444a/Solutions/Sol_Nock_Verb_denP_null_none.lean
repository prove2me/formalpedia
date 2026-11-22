-- Prove2me | solution 1 for Nock.Verb.denP_null_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:55.254829+00:00
-- url     : https://prove2.me/submissions/d2be1734-91d5-4f8d-98d1-9a54e53e7e9d

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
theorem _root_.solution {A B : Verb} {f : Nat} (hA : denP f A = none) :
    denP (f + 1) (Verb.node .null A B) = none := by
  simp only [denP, hA]
end Nock.Verb
