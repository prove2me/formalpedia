-- Prove2me | solution 1 for Nock.Verb.ev3P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:44.754771+00:00
-- url     : https://prove2.me/submissions/4f11143a-1b6f-422e-9881-5cfbad96cbe6

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
theorem _root_.solution {s1 f1 x1 s2 f2 x2 s3 f3 x3}
    (h1 : EvP s1 f1 x1) (h2 : EvP s2 f2 x2) (h3 : EvP s3 f3 x3) :
    ∃ f, evalPaper f s1 f1 = some x1 ∧ evalPaper f s2 f2 = some x2 ∧ evalPaper f s3 f3 = some x3 :=
      by
  obtain ⟨a, h1⟩ := h1; obtain ⟨b, h2⟩ := h2; obtain ⟨c, h3⟩ := h3
  exact ⟨max a (max b c), evalPaper_mono (by omega) h1, evalPaper_mono (by omega) h2,
    evalPaper_mono (by omega) h3⟩
end Nock.Verb
