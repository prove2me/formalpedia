-- Prove2me | solution 1 for Nock.Verb.den_star_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:44.150067+00:00
-- url     : https://prove2.me/submissions/1cdb530a-ace1-40ac-9c99-d4ed9e50faa7

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
theorem _root_.solution {A B : Verb} {f : Nat} {a b w : Noun}
    (hA : den f A = some a) (hB : den f B = some b) (he : evalN f a b = some w) :
    den (f + 1) (Verb.node .star A B) = some w := by
  simp only [den, hA, hB]; exact he
end Nock.Verb
