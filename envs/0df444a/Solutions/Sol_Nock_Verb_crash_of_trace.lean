-- Prove2me | solution 1 for Nock.Verb.crash_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:51.100287+00:00
-- url     : https://prove2.me/submissions/368fb15d-56af-4606-b71d-e88936e64649

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_eval_succ
public import Theorems.Thm_Nock_Verb_haltOutcome_crash


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution :
    ∀ (S : List Verb) (u w : Verb),
      S.head? = some u → Consistent S → S.getLast? = some w →
      next w = none → isTerminal w = false → eval S.length u = .crash
  | [], u, w, h, _, _, _, _ => by simp at h
  | [a], u, w, hh, _, hl, hnext, hnt => by
      simp only [List.head?_cons, Option.some.injEq] at hh
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hh; subst hl
      show eval 1 a = .crash
      rw [eval_succ, hnext, haltOutcome_crash hnt]
  | a :: b :: rest, u, w, hh, hc, hl, hnext, hnt => by
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      obtain ⟨hstep, hcrest⟩ := hc
      have hlrest : (b :: rest).getLast? = some w := by
        rw [List.getLast?_cons_cons] at hl; exact hl
      have ih := solution (b :: rest) b w rfl hcrest hlrest hnext hnt
      show eval ((b :: rest).length + 1) a = .crash
      rw [eval_succ, (hstep : next a = some b)]
      exact ih
end Nock.Verb
