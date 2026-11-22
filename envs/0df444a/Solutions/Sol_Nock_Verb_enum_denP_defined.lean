-- Prove2me | solution 1 for Nock.Verb.enum_denP_defined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:38.10537+00:00
-- url     : https://prove2.me/submissions/0ac74a57-6e27-4de9-8638-7755d3ba43d6

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_left_defined
public import Theorems.Thm_Nock_Verb_denP_right_defined_of_editOk
public import Theorems.Thm_Nock_Verb_editOk_children


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution :
    ∀ (v : Verb), editOk v = true → ∀ (c f : Nat) (x : Noun),
      denP f v = some x → ∀ p ∈ (enum v c).2, ∃ g y, denP g p.2 = some y := by
  intro v
  induction v with
  | leaf k => intro _ c f x _ p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro hok c f x hdenP p hp
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := by
        cases f with
        | zero => simp [denP] at hdenP
        | succ n => exact ⟨n, rfl⟩
      have hokl := (editOk_children hok).1
      have hokr := (editOk_children hok).2
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hleft | hright
      · subst hroot; exact ⟨f + 1, x, hdenP⟩
      · obtain ⟨yl, hyl⟩ := denP_left_defined hdenP
        exact ihl hokl (c + 1) f yl hyl p hleft
      · obtain ⟨g, yr, hyr⟩ := denP_right_defined_of_editOk hok hdenP
        exact ihr hokr _ g yr hyr p hright
end Nock.Verb
