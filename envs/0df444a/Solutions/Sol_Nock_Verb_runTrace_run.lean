-- Prove2me | solution 1 for Nock.Verb.runTrace_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:32.719803+00:00
-- url     : https://prove2.me/submissions/4a5e2393-6538-4d77-ac66-0ca482d5f13f

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
public import Theorems.Thm_Nock_Verb_runTrace_spec

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution :
    ∀ (fuel : Nat) (v : Verb) (T : List Verb), runTrace fuel v = some T →
      ∃ w, T.getLast? = some w ∧ run fuel v = result w := by
  intro fuel
  induction fuel with
  | zero => intro v T h; simp [runTrace] at h
  | succ fuel ih =>
      intro v T h
      simp only [runTrace] at h
      cases hn : next v with
      | none =>
          rw [hn] at h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨v, rfl, by simp only [run, hn]⟩
      | some v' =>
          rw [hn] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨T', hT', rfl⟩ := h
          obtain ⟨w, hw, hrun⟩ := ih v' T' hT'
          obtain ⟨rest, rfl⟩ : ∃ rest, T' = v' :: rest := by
            have hhead := (runTrace_spec fuel v' T' hT').1.1
            cases T' with
            | nil => simp at hhead
            | cons a t =>
                simp only [List.head?_cons, Option.some.injEq] at hhead
                exact ⟨t, by rw [hhead]⟩
          refine ⟨w, ?_, ?_⟩
          · rw [List.getLast?_cons_cons]; exact hw
          · simp only [run, hn]; exact hrun
end Nock.Verb
