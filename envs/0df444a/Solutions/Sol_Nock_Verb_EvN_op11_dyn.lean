-- Prove2me | solution 1 for Nock.Verb.EvN_op11_dyn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:11.8043+00:00
-- url     : https://prove2.me/submissions/2e11110d-6a66-4037-8e19-565c5ec897e3

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_ev2


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj tb clue body x} :
    Ev subj (.cell (.atom 11) (.cell (.cell tb clue) body)) x ↔
      (∃ cv, Ev subj clue cv) ∧ Ev subj body x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases hcv : evalN f subj clue with
      | none => rw [hcv] at h; simp at h
      | some cv => rw [hcv] at h; exact ⟨⟨cv, f, hcv⟩, f, h⟩
  · rintro ⟨⟨cv, hcv⟩, hbody⟩
    obtain ⟨f, hcv, hbody⟩ := ev2 hcv hbody
    exact ⟨f + 1, by simp only [evalN, hcv]; exact hbody⟩
end Nock.Verb
