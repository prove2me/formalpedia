-- Prove2me | solution 1 for Nock.Verb.EvP_op0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:34.594343+00:00
-- url     : https://prove2.me/submissions/3d5a2775-2709-41ea-8a22-b1b3c8ad427e

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
theorem _root_.solution {subj tail x} : EvP subj (.cell (.atom 0) tail) x ↔
    ∃ ax, tail = .atom ax ∧ Noun.slot ax subj = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom ax => exact ⟨ax, rfl, h⟩
      | cell => simp at h
  · rintro ⟨ax, rfl, hs⟩
    exact ⟨1, by simp only [evalPaper]; exact hs⟩
end Nock.Verb
