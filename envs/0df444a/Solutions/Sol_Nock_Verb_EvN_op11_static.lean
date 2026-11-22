-- Prove2me | solution 1 for Nock.Verb.EvN_op11_static
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:23.282008+00:00
-- url     : https://prove2.me/submissions/4159f986-d79b-46d8-9749-87615ecfad1b

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj t body x} :
    Ev subj (.cell (.atom 11) (.cell (.atom t) body)) x ↔ Ev subj body x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f => simp only [evalN] at h; exact ⟨f, h⟩
  · rintro ⟨fuel, h⟩; exact ⟨fuel + 1, by simp only [evalN]; exact h⟩
end Nock.Verb
