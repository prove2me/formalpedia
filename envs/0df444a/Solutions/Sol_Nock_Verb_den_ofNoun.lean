-- Prove2me | solution 1 for Nock.Verb.den_ofNoun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:12.79946+00:00
-- url     : https://prove2.me/submissions/c30672b0-78de-4813-a742-b70584a15924

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
theorem _root_.solution : ∀ (n : Noun) (fuel : Nat), n.size ≤ fuel → den fuel (ofNoun n) = some n := by
  intro n
  induction n with
  | atom k => intro fuel _; simp [ofNoun, den]
  | cell l r ihl ihr =>
      intro fuel hf
      simp only [Noun.size] at hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfl : l.size ≤ f := by omega
      have hfr : r.size ≤ f := by omega
      simp only [ofNoun, den, ihl f hfl, ihr f hfr]
end Nock.Verb
