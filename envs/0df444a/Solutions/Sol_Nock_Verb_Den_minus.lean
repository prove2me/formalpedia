-- Prove2me | solution 1 for Nock.Verb.Den_minus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:16.412566+00:00
-- url     : https://prove2.me/submissions/6584bb68-a0d1-488c-b99d-3fe303d47098

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
theorem _root_.solution {l r x} : Den (.node .minus l r) x ↔
    ∃ b, Den r b ∧ ((Den l (.atom 3) ∧ x = Noun.wut b) ∨ (Den l (.atom 4) ∧ Noun.lus b = some x)) :=
      by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      split at h
      · rename_i b hl hr
        exact ⟨b, ⟨f, hr⟩, Or.inl ⟨⟨f, hl⟩, (Option.some.inj h).symm⟩⟩
      · rename_i b hl hr
        exact ⟨b, ⟨f, hr⟩, Or.inr ⟨⟨f, hl⟩, h⟩⟩
      · simp at h
  · rintro ⟨b, hr, hor⟩
    rcases hor with ⟨hl, rfl⟩ | ⟨hl, hlus⟩
    · obtain ⟨f, hl, hr⟩ := den_pair hl hr
      exact ⟨f + 1, by simp only [den, hl, hr]⟩
    · obtain ⟨f, hl, hr⟩ := den_pair hl hr
      exact ⟨f + 1, by simp only [den, hl, hr]; exact hlus⟩
end Nock.Verb
