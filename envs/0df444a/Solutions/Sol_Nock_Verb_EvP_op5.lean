-- Prove2me | solution 1 for Nock.Verb.EvP_op5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:45.140193+00:00
-- url     : https://prove2.me/submissions/f6fd7d93-21c5-4aef-a3ab-326b43d966b3

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_ev2P

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj tail x} : EvP subj (.cell (.atom 5) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ EvP subj hb sb ∧ EvP subj hc sc ∧ x = Noun.tis sb sc := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom => simp at h
      | cell hb hc =>
        simp only at h
        split at h
        · rename_i sb sc hsb hsc
          exact ⟨hb, hc, sb, sc, rfl, ⟨f, hsb⟩, ⟨f, hsc⟩, (Option.some.inj h).symm⟩
        · simp at h
  · rintro ⟨hb, hc, sb, sc, rfl, hsb, hsc, rfl⟩
    obtain ⟨f, hsb, hsc⟩ := ev2P hsb hsc
    exact ⟨f + 1, by simp only [evalPaper, hsb, hsc]⟩
end Nock.Verb
