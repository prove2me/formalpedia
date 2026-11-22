-- Prove2me | solution 1 for Nock.Verb.ncost_align
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:26.159851+00:00
-- url     : https://prove2.me/submissions/6af44482-3e53-4be5-ab80-047c9c50641d

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_ncost_mono

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n m k : Nat} {a b r : Noun} (h : evalN n a b = some r)
    (hm : n ≤ m) (hk : n ≤ k) : ncost m a b = ncost k a b :=
  (ncost_mono hm h).trans (ncost_mono hk h).symm
end Nock.Verb
