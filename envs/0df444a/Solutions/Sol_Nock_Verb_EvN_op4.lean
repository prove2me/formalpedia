-- Prove2me | solution 1 for Nock.Verb.EvN_op4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:25.018717+00:00
-- url     : https://prove2.me/submissions/48bc545a-cf4e-4340-bdb6-f280c40ad187

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
theorem _root_.solution {subj tail x} : Ev subj (.cell (.atom 4) tail) x ↔
    ∃ y, Ev subj tail y ∧ Noun.lus y = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, hx⟩ := h
      exact ⟨y, ⟨f, hy⟩, hx⟩
  · rintro ⟨y, ⟨fy, hy⟩, hx⟩
    exact ⟨fy + 1, by simp only [evalN, hy]; exact hx⟩
end Nock.Verb
