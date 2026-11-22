-- Prove2me | solution 1 for Nock.Verb.op11_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:21.307365+00:00
-- url     : https://prove2.me/submissions/cba7905e-08c4-4034-a93d-f0e41dc1a560

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
theorem _root_.solution (A B : Nat) : 1 + A + (1 + 2 + B) = 4 + A + B := by omega
end Nock.Verb
