-- Prove2me | solution 1 for Nock.Verb.denP_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:20.782405+00:00
-- url     : https://prove2.me/submissions/24ccf9e4-aade-48c5-936d-e0829fc1f96b

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution : ∀ (v : Verb) (fuel : Nat),
    isTerminal v = true → v.noun.size ≤ fuel → denP fuel v = some v.noun := by
  intro v
  induction v with
  | leaf k => intro fuel _ _; simp [denP, noun]
  | node a l r ihl ihr =>
      intro fuel hterm hsize
      simp only [isTerminal, Bool.and_eq_true] at hterm
      obtain ⟨⟨hnull, hl⟩, hr⟩ := hterm
      have ha : a = Action.null := by cases a <;> simp_all only [Action.isNull, reduceCtorEq]
      subst ha
      simp only [noun, Noun.size] at hsize ⊢
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfl : l.noun.size ≤ f := by omega
      have hfr : r.noun.size ≤ f := by omega
      simp only [denP, ihl f hl hfl, ihr f hr hfr]
end Nock.Verb
