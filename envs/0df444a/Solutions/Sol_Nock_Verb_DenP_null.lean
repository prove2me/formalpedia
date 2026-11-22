-- Prove2me | solution 1 for Nock.Verb.DenP_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:48.002408+00:00
-- url     : https://prove2.me/submissions/32aaef0c-3b9e-4a7a-8362-df658693b1bb

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_pair

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l r x} : DenP (.node .null l r) x ↔ ∃ a b, x = .cell a b ∧ DenP l a ∧ DenP r b :=
  by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      cases hl : denP f l with
      | none => rw [hl] at h; simp at h
      | some a =>
        cases hr : denP f r with
        | none => rw [hl, hr] at h; simp at h
        | some b =>
          rw [hl, hr] at h; simp only [Option.some.injEq] at h
          exact ⟨a, b, h.symm, ⟨f, hl⟩, ⟨f, hr⟩⟩
  · rintro ⟨a, b, rfl, hl, hr⟩
    obtain ⟨f, hl, hr⟩ := denP_pair hl hr
    exact ⟨f + 1, by simp only [denP, hl, hr]⟩
end Nock.Verb
