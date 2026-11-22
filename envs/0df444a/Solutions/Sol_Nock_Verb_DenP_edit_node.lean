-- Prove2me | solution 1 for Nock.Verb.DenP_edit_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:08.890801+00:00
-- url     : https://prove2.me/submissions/88d10f42-6af5-47ed-8e43-a3324adde93a

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_triple

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l b nw od x} : DenP (.node .edit l (.node b nw od)) x ↔
    ∃ ax n o, DenP l (.atom ax) ∧ DenP nw n ∧ DenP od o ∧ Noun.edit ax n o = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      split at h
      · rename_i ax n o hl hnw hod
        exact ⟨ax, n, o, ⟨f, hl⟩, ⟨f, hnw⟩, ⟨f, hod⟩, h⟩
      · simp at h
  · rintro ⟨ax, n, o, hl, hnw, hod, he⟩
    obtain ⟨f, hl, hnw, hod⟩ := denP_triple hl hnw hod
    exact ⟨f + 1, by simp only [denP, hl, hnw, hod]; exact he⟩
end Nock.Verb
