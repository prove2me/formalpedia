-- Prove2me | solution 1 for Nock.Verb.DenP_minus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:55.115889+00:00
-- url     : https://prove2.me/submissions/f3527af7-01bf-4294-9609-ede50158ec49

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
theorem _root_.solution {l r x} : DenP (.node .minus l r) x ↔
    ∃ b, DenP r b ∧ ((DenP l (.atom 3) ∧ x = Noun.wut b) ∨ (DenP l (.atom 4) ∧ Noun.lus b = some x))
      := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      split at h
      · rename_i b hl hr
        exact ⟨b, ⟨f, hr⟩, Or.inl ⟨⟨f, hl⟩, (Option.some.inj h).symm⟩⟩
      · rename_i b hl hr
        exact ⟨b, ⟨f, hr⟩, Or.inr ⟨⟨f, hl⟩, h⟩⟩
      · simp at h
  · rintro ⟨b, hr, hor⟩
    rcases hor with ⟨hl, rfl⟩ | ⟨hl, hlus⟩
    · obtain ⟨f, hl, hr⟩ := denP_pair hl hr
      exact ⟨f + 1, by simp only [denP, hl, hr]⟩
    · obtain ⟨f, hl, hr⟩ := denP_pair hl hr
      exact ⟨f + 1, by simp only [denP, hl, hr]; exact hlus⟩
end Nock.Verb
