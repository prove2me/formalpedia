-- Prove2me | solution 1 for Nock.Verb.EvP_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:05.453381+00:00
-- url     : https://prove2.me/submissions/d9f525f8-a9ee-422f-b44d-dda751718865

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_evalPaper_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a b y1 y2 : Noun} (h1 : EvP a b y1) (h2 : EvP a b y2) : y1 = y2 := by
  obtain ⟨f1, h1⟩ := h1; obtain ⟨f2, h2⟩ := h2
  exact Option.some.inj ((evalPaper_mono (Nat.le_max_left f1 f2) h1).symm.trans
    (evalPaper_mono (Nat.le_max_right f1 f2) h2))
end Nock.Verb
