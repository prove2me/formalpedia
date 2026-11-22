-- Prove2me | solution 1 for Nock.Verb.EvN_autocons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:35.44806+00:00
-- url     : https://prove2.me/submissions/7eb08e7b-19d0-4533-8f97-22220ca7a8e6

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_ev2

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj hb hc d x} : Ev subj (.cell (.cell hb hc) d) x ↔
    ∃ l r, x = .cell l r ∧ Ev subj (.cell hb hc) l ∧ Ev subj d r := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      split at h
      · rename_i l r hl hr
        exact ⟨l, r, (Option.some.inj h).symm, ⟨f, hl⟩, ⟨f, hr⟩⟩
      · simp at h
  · rintro ⟨l, r, rfl, hl, hr⟩
    obtain ⟨f, hl, hr⟩ := ev2 hl hr
    exact ⟨f + 1, by simp only [evalN, hl, hr]⟩
end Nock.Verb
