-- Prove2me | solution 1 for Nock.Verb.den_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:35.329808+00:00
-- url     : https://prove2.me/submissions/da494693-eea8-4b3d-b0b8-9599b736632a

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution : ∀ (v : Verb) (fuel : Nat),
    isTerminal v = true → v.noun.size ≤ fuel → den fuel v = some v.noun := by
  intro v
  induction v with
  | leaf k => intro fuel _ _; simp [den, noun]
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
      simp only [den, ihl f hl hfl, ihr f hr hfr]
end Nock.Verb
