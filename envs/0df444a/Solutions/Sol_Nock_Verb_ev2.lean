-- Prove2me | solution 1 for Nock.Verb.ev2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:52.620537+00:00
-- url     : https://prove2.me/submissions/00c1b7bc-1cc7-4d74-8add-69edaecca422

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_evalN_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {s1 f1 x1 s2 f2 x2} (h1 : Ev s1 f1 x1) (h2 : Ev s2 f2 x2) :
    ∃ f, evalN f s1 f1 = some x1 ∧ evalN f s2 f2 = some x2 := by
  obtain ⟨a, h1⟩ := h1; obtain ⟨b, h2⟩ := h2
  exact ⟨max a b, evalN_mono (Nat.le_max_left _ _) h1, evalN_mono (Nat.le_max_right _ _) h2⟩
end Nock.Verb
