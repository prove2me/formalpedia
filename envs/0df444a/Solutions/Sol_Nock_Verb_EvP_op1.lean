-- Prove2me | solution 1 for Nock.Verb.EvP_op1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:50.362208+00:00
-- url     : https://prove2.me/submissions/5cc2c46e-9b02-4385-af55-5df1fb1bc2a6

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
theorem _root_.solution {subj tail x} : EvP subj (.cell (.atom 1) tail) x ↔ x = tail := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f => simp only [evalPaper] at h; exact (Option.some.inj h).symm
  · rintro rfl; exact ⟨1, by simp only [evalPaper]⟩
end Nock.Verb
