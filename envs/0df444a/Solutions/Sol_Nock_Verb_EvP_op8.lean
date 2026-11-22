-- Prove2me | solution 1 for Nock.Verb.EvP_op8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:50.477858+00:00
-- url     : https://prove2.me/submissions/173a7e68-1c74-45fe-9d97-2c96f8712c3c

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
theorem _root_.solution {subj tail x} : EvP subj (.cell (.atom 8) tail) x ↔
    ∃ hb hc sb, tail = .cell hb hc ∧ EvP subj hb sb ∧ EvP (.cell sb subj) hc x := by
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
        cases hsb : evalPaper f subj hb with
        | none => rw [hsb] at h; simp at h
        | some sb => rw [hsb] at h; exact ⟨hb, hc, sb, rfl, ⟨f, hsb⟩, ⟨f, h⟩⟩
  · rintro ⟨hb, hc, sb, rfl, hsb, hx⟩
    obtain ⟨f, hsb, hx⟩ := ev2P hsb hx
    exact ⟨f + 1, by simp only [evalPaper, hsb]; exact hx⟩
end Nock.Verb
