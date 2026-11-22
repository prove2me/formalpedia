-- Prove2me | solution 1 for Nock.Verb.replaceAux_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:00.79507+00:00
-- url     : https://prove2.me/submissions/98d90664-d23d-4ae3-ab79-7d8266f8a43e

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_findAt_append
public import Theorems.Thm_Nock_Verb_replaceAux_counter


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (i : Nat) (r₀ : Verb) : ∀ (v : Verb) (c : Nat),
    findAt i (enum v c).2 = none → (replaceAux i r₀ v c).2 = v := by
  intro v
  induction v with
  | leaf k => intro c _; rfl
  | node a l r ihl ihr =>
      intro c hnone
      have hci : i ≠ c := by
        intro h; subst h; simp [enum, findAt] at hnone
      have hine : ¬ (c = i) := fun h => hci h.symm
      simp only [enum, findAt, if_neg (fun h : i = c => hci h)] at hnone
      rw [findAt_append] at hnone
      have hln : findAt i (enum l (c + 1)).2 = none := by
        cases hl : findAt i (enum l (c + 1)).2 with
        | none => rfl
        | some s => rw [hl] at hnone; simp at hnone
      have hrn : findAt i (enum r (enum l (c + 1)).1).2 = none := by
        rw [hln] at hnone; exact hnone
      have hcL : (replaceAux i r₀ l (c + 1)).1 = (enum l (c + 1)).1 := replaceAux_counter i r₀ l (c
        + 1)
      simp only [replaceAux, if_neg hine]
      rw [ihl (c + 1) hln, hcL, ihr _ hrn]
end Nock.Verb
