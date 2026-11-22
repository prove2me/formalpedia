-- Prove2me | solution 1 for Nock.Verb.EvP_op2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:20.0447+00:00
-- url     : https://prove2.me/submissions/2243f09f-de48-4d00-ad75-db9b5fd1dc06

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_ev3P

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj tail x} : EvP subj (.cell (.atom 2) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ EvP subj hb sb ∧ EvP subj hc sc ∧ EvP sb sc x := by
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
          exact ⟨hb, hc, sb, sc, rfl, ⟨f, hsb⟩, ⟨f, hsc⟩, ⟨f, h⟩⟩
        · simp at h
  · rintro ⟨hb, hc, sb, sc, rfl, hsb, hsc, hx⟩
    obtain ⟨f, hsb, hsc, hx⟩ := ev3P hsb hsc hx
    exact ⟨f + 1, by simp only [evalPaper, hsb, hsc]; exact hx⟩
end Nock.Verb
