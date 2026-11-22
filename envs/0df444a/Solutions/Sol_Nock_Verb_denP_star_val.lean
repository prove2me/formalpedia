-- Prove2me | solution 1 for Nock.Verb.denP_star_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:44.672378+00:00
-- url     : https://prove2.me/submissions/21a773b7-cd22-42e6-9227-b91ebdd3401d

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
theorem _root_.solution {A B : Verb} {f : Nat} {a b w : Noun}
    (hA : denP f A = some a) (hB : denP f B = some b) (he : evalPaper f a b = some w) :
    denP (f + 1) (Verb.node .star A B) = some w := by
  simp only [denP, hA, hB]; exact he
end Nock.Verb
