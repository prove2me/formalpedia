-- Prove2me | solution 1 for Nock.Verb.ev2P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:53.10423+00:00
-- url     : https://prove2.me/submissions/6cbd23ed-ffa2-43ae-84bf-11ad43536dab

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_evalPaper_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {s1 f1 x1 s2 f2 x2} (h1 : EvP s1 f1 x1) (h2 : EvP s2 f2 x2) :
    ∃ f, evalPaper f s1 f1 = some x1 ∧ evalPaper f s2 f2 = some x2 := by
  obtain ⟨a, h1⟩ := h1; obtain ⟨b, h2⟩ := h2
  exact ⟨max a b, evalPaper_mono (Nat.le_max_left _ _) h1, evalPaper_mono (Nat.le_max_right _ _) h2⟩
end Nock.Verb
