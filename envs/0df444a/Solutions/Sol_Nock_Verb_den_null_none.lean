-- Prove2me | solution 1 for Nock.Verb.den_null_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:44.544809+00:00
-- url     : https://prove2.me/submissions/89dbebe3-7be5-4290-abc6-69aab177600e

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
theorem _root_.solution {A B : Verb} {f : Nat} (hA : den f A = none) :
    den (f + 1) (Verb.node .null A B) = none := by
  simp only [den, hA]
end Nock.Verb
