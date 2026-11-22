-- Prove2me | solution 1 for Nock.Verb.equiv_continuations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:21.307105+00:00
-- url     : https://prove2.me/submissions/75c5e336-5729-4c88-b4cf-6e21dbcc570e

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
section
@[expose] public section
namespace Nock
namespace Verb
private theorem head?_some_mem {F : Verb} {T : List Verb}
    (h : T.head? = some F) : F ∈ T := by
  cases T with
  | nil => simp at h
  | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h; simp
private theorem getLast?_cons₂ (x y : Verb) (t : List Verb) :
    (x :: y :: t).getLast? = (y :: t).getLast? := by
  simp [List.getLast?_cons_cons]
private theorem consistent_suffix_of_mem {F : Verb} :
    ∀ (T : List Verb), Consistent T → F ∈ T →
      ∃ S, S.head? = some F ∧ Consistent S ∧ S.getLast? = T.getLast? := by
  intro T
  induction T with
  | nil => intro _ hmem; simp at hmem
  | cons a t iht =>
      cases t with
      | nil =>
          intro hc hmem
          simp only [List.mem_singleton] at hmem
          subst hmem
          exact ⟨[F], by simp, hc, rfl⟩
      | cons b t' =>
          intro hc hmem
          obtain ⟨hab, hrest⟩ := hc
          rcases List.mem_cons.1 hmem with hFa | hmem'
          · subst hFa
            exact ⟨F :: b :: t', by simp, ⟨hab, hrest⟩, rfl⟩
          · obtain ⟨S, hS1, hS2, hS3⟩ := iht hrest hmem'
            exact ⟨S, hS1, hS2, hS3.trans (getLast?_cons₂ a b t').symm⟩
end Verb
end Nock
end
end

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution (F : Verb) : Finite F ↔ FiniteTransition F := by
  constructor
  · rintro ⟨T, hTof, hComp⟩
    exact ⟨F, T, hTof, hComp, head?_some_mem hTof.1⟩
  · rintro ⟨F0, T, hTof, ⟨v, hlast, hnext⟩, hmem⟩
    obtain ⟨S, hS1, hS2, hS3⟩ := consistent_suffix_of_mem T hTof.2 hmem
    exact ⟨S, ⟨hS1, hS2⟩, ⟨v, hS3.trans hlast, hnext⟩⟩
end Nock.Verb
