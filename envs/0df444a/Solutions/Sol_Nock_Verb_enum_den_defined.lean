-- Prove2me | solution 1 for Nock.Verb.enum_den_defined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:01.271907+00:00
-- url     : https://prove2.me/submissions/aefc3b06-2adb-4a85-9846-834bb813e92f

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_den_left_defined
public import Theorems.Thm_Nock_Verb_den_right_defined_of_editOk
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
      den f v = some x → ∀ p ∈ (enum v c).2, ∃ g y, den g p.2 = some y := by
  intro v
  induction v with
  | leaf k => intro _ c f x _ p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro hok c f x hden p hp
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := by
        cases f with
        | zero => simp [den] at hden
        | succ n => exact ⟨n, rfl⟩
      have hokl := (editOk_children hok).1
      have hokr := (editOk_children hok).2
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hleft | hright
      · subst hroot; exact ⟨f + 1, x, hden⟩
      · obtain ⟨yl, hyl⟩ := den_left_defined hden
        exact ihl hokl (c + 1) f yl hyl p hleft
      · obtain ⟨g, yr, hyr⟩ := den_right_defined_of_editOk hok hden
        exact ihr hokr _ g yr hyr p hright
end Nock.Verb
