-- Prove2me | solution 1 for Nock.Verb.EvP_autocons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:46.429515+00:00
-- url     : https://prove2.me/submissions/94da7e3b-d811-4172-8f8a-af066ca15d13

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
theorem _root_.solution {subj hb hc d x} : EvP subj (.cell (.cell hb hc) d) x ↔
    ∃ l r, x = .cell l r ∧ EvP subj (.cell hb hc) l ∧ EvP subj d r := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      split at h
      · rename_i l r hl hr
        exact ⟨l, r, (Option.some.inj h).symm, ⟨f, hl⟩, ⟨f, hr⟩⟩
      · simp at h
  · rintro ⟨l, r, rfl, hl, hr⟩
    obtain ⟨f, hl, hr⟩ := ev2P hl hr
    exact ⟨f + 1, by simp only [evalPaper, hl, hr]⟩
end Nock.Verb
