-- Prove2me | solution 1 for Nock.Verb.runTrace_final_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:40.393169+00:00
-- url     : https://prove2.me/submissions/4e9d58a2-f7d1-42d7-8ee6-008497d0c899

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
public import Theorems.Thm_Nock_Verb_runTrace_complete
public import Theorems.Thm_Nock_Verb_getIndex_none_iff_terminal
public import Theorems.Thm_Nock_Verb_nockCheck_eq_true_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) :
    ∃ w, T.getLast? = some w ∧ (isTerminal w = true ∨ NockCheck w none = true) := by
  obtain ⟨w, hw, hwn⟩ := runTrace_complete h
  refine ⟨w, hw, ?_⟩
  by_cases ht : isTerminal w = true
  · exact Or.inl ht
  · refine Or.inr (nockCheck_eq_true_iff.mpr (Or.inr ⟨rfl, ?_⟩))
    have hgi : getIndex w ≠ none := fun hg => ht (getIndex_none_iff_terminal.mp hg)
    exact ⟨hgi, hwn⟩
end Nock.Verb
