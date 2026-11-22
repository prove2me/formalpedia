-- Prove2me | solution 1 for Nock.Verb.Den_equal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:40.682779+00:00
-- url     : https://prove2.me/submissions/dbbc051d-45f5-48f0-96ec-a61f6ef2b55a

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_pair

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l r x} : Den (.node .equal l r) x ↔
    ∃ a b, Den l a ∧ Den r b ∧ x = Noun.tis a b := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      split at h
      · rename_i a b hl hr
        exact ⟨a, b, ⟨f, hl⟩, ⟨f, hr⟩, (Option.some.inj h).symm⟩
      · simp at h
  · rintro ⟨a, b, hl, hr, rfl⟩
    obtain ⟨f, hl, hr⟩ := den_pair hl hr
    exact ⟨f + 1, by simp only [den, hl, hr]⟩
end Nock.Verb
