-- Prove2me | solution 1 for Nock.Verb.DenP_equal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:48.853162+00:00
-- url     : https://prove2.me/submissions/04c73b57-aacc-4cd7-8b1c-530c6c7f013d

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
theorem _root_.solution {l r x} : DenP (.node .equal l r) x ↔
    ∃ a b, DenP l a ∧ DenP r b ∧ x = Noun.tis a b := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      split at h
      · rename_i a b hl hr
        exact ⟨a, b, ⟨f, hl⟩, ⟨f, hr⟩, (Option.some.inj h).symm⟩
      · simp at h
  · rintro ⟨a, b, hl, hr, rfl⟩
    obtain ⟨f, hl, hr⟩ := denP_pair hl hr
    exact ⟨f + 1, by simp only [denP, hl, hr]⟩
end Nock.Verb
