-- Prove2me | solution 1 for Nock.Verb.denP_null_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:36.437262+00:00
-- url     : https://prove2.me/submissions/a3abb169-02ca-44b0-96fe-1edcea0c2dd8

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
theorem _root_.solution {A B : Verb} {f : Nat} {a b : Noun}
    (hA : denP f A = some a) (hB : denP f B = some b) :
    denP (f + 1) (Verb.node .null A B) = some (Noun.cell a b) := by
  simp only [denP, hA, hB]
end Nock.Verb
