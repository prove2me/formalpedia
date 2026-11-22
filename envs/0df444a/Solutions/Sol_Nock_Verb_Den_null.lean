-- Prove2me | solution 1 for Nock.Verb.Den_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:39.030679+00:00
-- url     : https://prove2.me/submissions/78171f9c-33a2-40d9-9a14-4a1ecbdc5416

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
theorem _root_.solution {l r x} : Den (.node .null l r) x ↔ ∃ a b, x = .cell a b ∧ Den l a ∧ Den r b := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      cases hl : den f l with
      | none => rw [hl] at h; simp at h
      | some a =>
        cases hr : den f r with
        | none => rw [hl, hr] at h; simp at h
        | some b =>
          rw [hl, hr] at h; simp only [Option.some.injEq] at h
          exact ⟨a, b, h.symm, ⟨f, hl⟩, ⟨f, hr⟩⟩
  · rintro ⟨a, b, rfl, hl, hr⟩
    obtain ⟨f, hl, hr⟩ := den_pair hl hr
    exact ⟨f + 1, by simp only [den, hl, hr]⟩
end Nock.Verb
