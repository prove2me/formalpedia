-- Prove2me | solution 1 for Nock.Verb.runTrace_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:41.625224+00:00
-- url     : https://prove2.me/submissions/19a53b5a-4810-474f-adf6-bc17ce542f5a

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution :
    ∀ (fuel : Nat) (v : Verb) (T : List Verb), runTrace fuel v = some T →
      TraceOf v T ∧ Complete T := by
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
          exact ⟨⟨rfl, trivial⟩, ⟨v, rfl, hn⟩⟩
      | some v' =>
          rw [hn] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨T', hT', rfl⟩ := h
          obtain ⟨⟨hhead, hcons⟩, hcomp⟩ := ih v' T' hT'
          obtain ⟨rest, rfl⟩ : ∃ rest, T' = v' :: rest := by
            cases T' with
            | nil => simp at hhead
            | cons a t =>
                simp only [List.head?_cons, Option.some.injEq] at hhead
                exact ⟨t, by rw [hhead]⟩
          refine ⟨⟨rfl, ⟨hn, hcons⟩⟩, ?_⟩
          obtain ⟨w, hw, hwn⟩ := hcomp
          exact ⟨w, by rw [List.getLast?_cons_cons, hw], hwn⟩
end Nock.Verb
