-- Prove2me | solution 1 for Nock.Verb.Den_edit_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:43.19399+00:00
-- url     : https://prove2.me/submissions/3ad0bfe7-5315-4b3d-8c7a-8b7722a74160

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_triple

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l b nw od x} : Den (.node .edit l (.node b nw od)) x ↔
    ∃ ax n o, Den l (.atom ax) ∧ Den nw n ∧ Den od o ∧ Noun.edit ax n o = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      split at h
      · rename_i ax n o hl hnw hod
        exact ⟨ax, n, o, ⟨f, hl⟩, ⟨f, hnw⟩, ⟨f, hod⟩, h⟩
      · simp at h
  · rintro ⟨ax, n, o, hl, hnw, hod, he⟩
    obtain ⟨f, hl, hnw, hod⟩ := den_triple hl hnw hod
    exact ⟨f + 1, by simp only [den, hl, hnw, hod]; exact he⟩
end Nock.Verb
