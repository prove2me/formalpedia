-- Prove2me | solution 1 for Nock.Verb.runHintProgram_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:03.412818+00:00
-- url     : https://prove2.me/submissions/6bd73829-47c1-4e71-a2a5-8f59b80564a9

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_runHint_sound
public import Theorems.Thm_Nock_Verb_den_iff_evalN
public import Theorems.Thm_Nock_Verb_editOk_program


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {s f r : Noun} {fuel : Nat}
    (h : runHintProgram fuel s f = some r) : ∃ fuel', evalN fuel' s f = some r := by
  have : ∃ f', den f' (program s f) = some r := runHint_sound fuel (editOk_program s f) h
  exact (den_iff_evalN s f r).1 this
end Nock.Verb
