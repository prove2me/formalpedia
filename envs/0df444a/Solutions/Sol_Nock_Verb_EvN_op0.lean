-- Prove2me | solution 1 for Nock.Verb.EvN_op0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:46.792985+00:00
-- url     : https://prove2.me/submissions/941ec6c5-5c5f-4b4b-9386-837704d3c7ee

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj tail x} : Ev subj (.cell (.atom 0) tail) x ↔
    ∃ ax, tail = .atom ax ∧ Noun.slot ax subj = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom ax => exact ⟨ax, rfl, h⟩
      | cell => simp at h
  · rintro ⟨ax, rfl, hs⟩
    exact ⟨1, by simp only [evalN]; exact hs⟩
end Nock.Verb
