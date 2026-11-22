-- Prove2me | solution 1 for Nock.Verb.trace_unique_of_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:27.258415+00:00
-- url     : https://prove2.me/submissions/fa306282-2a26-4694-862e-47767b1fdeeb

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {R : Verb → Verb → Prop}
    (hdet : ∀ {a b b' : Verb}, R a b → R a b' → b = b') :
    ∀ (T1 T2 : List Verb), ConsistentR R T1 → ConsistentR R T2 →
      T1.head? = T2.head? → T1.length = T2.length → T1 = T2 := by
  intro T1
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
                  simp only [ConsistentR] at h1 h2
                  obtain ⟨hab, hbt⟩ := h1
                  obtain ⟨had, hdt⟩ := h2
                  have hbd : b = d := hdet hab had
                  subst hbd
                  have hrec : (b :: t1') = (b :: t2') :=
                    ih (b :: t2') hbt hdt (by simp)
                      (by simp only [List.length_cons] at hl ⊢; omega)
                  exact congrArg (a :: ·) hrec
end Nock.Verb
