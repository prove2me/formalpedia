-- Prove2me | solution 1 for Nock.Verb.den_null_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:38.203743+00:00
-- url     : https://prove2.me/submissions/2809bf7a-de98-4837-9501-e57b3631a4f6

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
theorem _root_.solution {A B : Verb} {f : Nat} {a b : Noun}
    (hA : den f A = some a) (hB : den f B = some b) :
    den (f + 1) (Verb.node .null A B) = some (Noun.cell a b) := by
  simp only [den, hA, hB]
end Nock.Verb
