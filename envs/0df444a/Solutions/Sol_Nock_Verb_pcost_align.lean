-- Prove2me | solution 1 for Nock.Verb.pcost_align
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:43.972352+00:00
-- url     : https://prove2.me/submissions/680bb3d8-daf1-4a89-8fbd-f71904d6021f

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_pcost_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n m k : Nat} {a b r : Noun} (h : evalPaper n a b = some r)
    (hm : n ≤ m) (hk : n ≤ k) : pcost m a b = pcost k a b :=
  (pcost_mono hm h).trans (pcost_mono hk h).symm
end Nock.Verb
