-- Prove2me | solution 1 for Nock.Verb.eval_crash_checked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:47.569978+00:00
-- url     : https://prove2.me/submissions/275fc61a-565c-4089-b933-a7ef7232fe35

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_eval_crash_invalid
public import Theorems.Thm_Nock_Verb_getIndex_none_iff_terminal
public import Theorems.Thm_Nock_Verb_nockCheck_eq_true_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {n : Nat} {v : Verb} (h : eval n v = .crash) :
    ∃ T w, TraceOf v T ∧ T.getLast? = some w ∧ Crashes w ∧ NockCheck w none = true := by
  obtain ⟨T, w, hTr, hlast, hnext, hnt⟩ := eval_crash_invalid h
  have hgi : getIndex w ≠ none := fun hg =>
    absurd (getIndex_none_iff_terminal.mp hg) (by simp [hnt])
  have hcr : Crashes w := ⟨hgi, hnext⟩
  exact ⟨T, w, hTr, hlast, hcr, nockCheck_eq_true_iff.mpr (Or.inr ⟨rfl, hcr⟩)⟩
end Nock.Verb
