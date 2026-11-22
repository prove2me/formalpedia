-- Prove2me | solution 1 for Nock.Verb.denP_ofNoun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:41.341263+00:00
-- url     : https://prove2.me/submissions/316d3c73-4c39-4173-bce8-1b63f0adc20b

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
theorem _root_.solution : ∀ (n : Noun) (fuel : Nat), n.size ≤ fuel → denP fuel (ofNoun n) = some n := by
  intro n
  induction n with
  | atom k => intro fuel _; simp [ofNoun, denP]
  | cell l r ihl ihr =>
      intro fuel hf
      simp only [Noun.size] at hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfl : l.size ≤ f := by omega
      have hfr : r.size ≤ f := by omega
      simp only [ofNoun, denP, ihl f hfl, ihr f hfr]
end Nock.Verb
