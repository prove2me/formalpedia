-- Prove2me | solution 1 for Nock.Verb.eval_crash_invalid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:54.664363+00:00
-- url     : https://prove2.me/submissions/c80946d5-103c-4de3-9d77-5f5ebe24de3c

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_eval_succ


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {n : Nat} {v : Verb} (h : eval n v = .crash) : Invalid v := by
  induction n generalizing v with
  | zero => simp [eval] at h
  | succ n ih =>
      rw [eval_succ] at h
      cases hnv : next v with
      | some v' =>
          simp only [hnv] at h
          obtain ⟨T, w, hTr, hlast, hnext, hnt⟩ := ih h
          refine ⟨v :: T, w, ?_, ?_, hnext, hnt⟩
          · refine ⟨rfl, ?_⟩
            obtain ⟨hhead, hcons⟩ := hTr
            cases T with
            | nil => simp at hhead
            | cons a t =>
                simp only [List.head?_cons, Option.some.injEq] at hhead
                subst hhead
                exact ⟨hnv, hcons⟩
          · obtain ⟨hhead, _⟩ := hTr
            cases T with
            | nil => simp at hhead
            | cons a t => simp [List.getLast?_cons_cons] at hlast ⊢; exact hlast
      | none =>
          simp only [hnv, haltOutcome] at h
          have hnt : v.isTerminal = false := by
            by_cases ht : v.isTerminal
            · rw [if_pos ht] at h; exact Outcome.noConfusion h
            · simpa using ht
          exact ⟨[v], v, ⟨rfl, trivial⟩, rfl, hnv, hnt⟩
end Nock.Verb
