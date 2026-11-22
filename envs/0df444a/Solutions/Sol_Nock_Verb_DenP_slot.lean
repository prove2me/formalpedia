-- Prove2me | solution 1 for Nock.Verb.DenP_slot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:49.440931+00:00
-- url     : https://prove2.me/submissions/e2c5c8dd-3936-41e6-bfed-9da97065d74c

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
theorem _root_.solution {l r x} : DenP (.node .slot l r) x ↔
    ∃ ax b, DenP l (.atom ax) ∧ DenP r b ∧ Noun.slot ax b = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      split at h
      · rename_i ax b hl hr
        exact ⟨ax, b, ⟨f, hl⟩, ⟨f, hr⟩, h⟩
      · simp at h
  · rintro ⟨ax, b, hl, hr, hs⟩
    obtain ⟨f, hl, hr⟩ := denP_pair hl hr
    exact ⟨f + 1, by simp only [denP, hl, hr]; exact hs⟩
end Nock.Verb
