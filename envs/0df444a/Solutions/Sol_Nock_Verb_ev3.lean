-- Prove2me | solution 1 for Nock.Verb.ev3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:20.590465+00:00
-- url     : https://prove2.me/submissions/5faf77f9-e032-4000-b2a6-efe227d217fe

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
theorem _root_.solution {s1 f1 x1 s2 f2 x2 s3 f3 x3} (h1 : Ev s1 f1 x1) (h2 : Ev s2 f2 x2) (h3 : Ev s3 f3 x3) :
    ∃ f, evalN f s1 f1 = some x1 ∧ evalN f s2 f2 = some x2 ∧ evalN f s3 f3 = some x3 := by
  obtain ⟨a, h1⟩ := h1; obtain ⟨b, h2⟩ := h2; obtain ⟨c, h3⟩ := h3
  exact ⟨max a (max b c), evalN_mono (by omega) h1, evalN_mono (by omega) h2, evalN_mono (by omega)
    h3⟩
end Nock.Verb
