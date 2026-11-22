-- Prove2me | solution 1 for Nock.Verb.EvN_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:21.621806+00:00
-- url     : https://prove2.me/submissions/53db9e07-aa23-4bd3-ac7a-dda8a427f5d1

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_evalN_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a b y1 y2 : Noun} (h1 : Ev a b y1) (h2 : Ev a b y2) : y1 = y2 := by
  obtain ⟨f1, h1⟩ := h1; obtain ⟨f2, h2⟩ := h2
  exact Option.some.inj ((evalN_mono (Nat.le_max_left f1 f2) h1).symm.trans
    (evalN_mono (Nat.le_max_right f1 f2) h2))
end Nock.Verb
