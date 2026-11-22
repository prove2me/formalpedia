-- Prove2me | solution 1 for Nock.Verb.EvN_op3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:51.863597+00:00
-- url     : https://prove2.me/submissions/51a30203-39b8-4f4c-b634-0a0ae5ce8a32

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
theorem _root_.solution {subj tail x} : Ev subj (.cell (.atom 3) tail) x ↔
    ∃ y, Ev subj tail y ∧ x = Noun.wut y := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, hx⟩ := h
      exact ⟨y, ⟨f, hy⟩, hx.symm⟩
  · rintro ⟨y, ⟨fy, hy⟩, rfl⟩
    exact ⟨fy + 1, by simp only [evalN, hy, Option.map_some]⟩
end Nock.Verb
