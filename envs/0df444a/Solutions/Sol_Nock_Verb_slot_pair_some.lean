-- Prove2me | solution 1 for Nock.Verb.slot_pair_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:52.4508+00:00
-- url     : https://prove2.me/submissions/05ad6ef9-793c-46fc-ac6f-6531959bf4f2

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_slot_two
public import Theorems.Thm_Nock_Verb_slot_three

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {p q : Nat} : ∀ (m : Nat) (v : Noun),
    Noun.slot m (.cell (.atom p) (.atom q)) = some v → m = 1 ∨ m = 2 ∨ m = 3 := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro v hv
    match m with
    | 0 => simp [Noun.slot] at hv
    | 1 => exact Or.inl rfl
    | 2 => exact Or.inr (Or.inl rfl)
    | 3 => exact Or.inr (Or.inr rfl)
    | (k+4) =>
        exfalso
        rw [Noun.slot] at hv
        cases hs : Noun.slot ((k+4)/2) (.cell (.atom p) (.atom q)) with
        | none => rw [hs] at hv; simp at hv
        | some w =>
            rw [hs] at hv
            rcases ih ((k+4)/2) (by omega) w hs with h1 | h2 | h3
            · omega
            · rw [h2, slot_two] at hs; obtain rfl := Option.some.inj hs; simp at hv
            · rw [h3, slot_three] at hs; obtain rfl := Option.some.inj hs; simp at hv
end Nock.Verb
