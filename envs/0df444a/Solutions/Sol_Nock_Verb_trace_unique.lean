-- Prove2me | solution 1 for Nock.Verb.trace_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:26.753299+00:00
-- url     : https://prove2.me/submissions/d5e66efe-5df4-4ce6-82a5-f7622f069b94

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_Step_det
public import Theorems.Thm_Nock_Verb_SelStep_det


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution (T1 : List Verb) : ∀ (T2 : List Verb),
    Consistent T1 → Consistent T2 → T1.head? = T2.head? → T1.length = T2.length → T1 = T2 := by
  induction T1 with
  | nil =>
      intro T2 _ _ _ hl
      cases T2 with
      | nil => rfl
      | cons _ _ => simp at hl
  | cons a t1 ih =>
      intro T2 h1 h2 hh hl
      cases T2 with
      | nil => simp at hl
      | cons c t2 =>
          have hac : a = c := by
            simp only [List.head?_cons, Option.some.injEq] at hh; exact hh
          subst hac
          cases t1 with
          | nil =>
              cases t2 with
              | nil => rfl
              | cons _ _ => simp at hl
          | cons b t1' =>
              cases t2 with
              | nil => simp at hl
              | cons d t2' =>
                  simp only [Consistent] at h1 h2
                  obtain ⟨hab, hbt⟩ := h1
                  obtain ⟨had, hdt⟩ := h2
                  have hbd : b = d := Step.det hab had
                  subst hbd
                  have hrec : (b :: t1') = (b :: t2') :=
                    ih (b :: t2') hbt hdt (by simp)
                      (by simp only [List.length_cons] at hl ⊢; omega)
                  exact congrArg (a :: ·) hrec
end Nock.Verb
