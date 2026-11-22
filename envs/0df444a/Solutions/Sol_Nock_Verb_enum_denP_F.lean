-- Prove2me | solution 1 for Nock.Verb.enum_denP_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:31.6927+00:00
-- url     : https://prove2.me/submissions/a1872888-b4ec-45c2-974a-2c4bddbec64f

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_denP_children_F
public import Theorems.Thm_Nock_Verb_editOk_children


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} : ∀ (v : Verb), editOk v = true → ∀ (c : Nat) (x : Noun),
    denP F v = some x → ∀ p ∈ (enum v c).2, ∃ y, denP F p.2 = some y := by
  intro v
  induction v with
  | leaf k => intro _ c x _ p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro hok c x hd p hp
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := denP_children_F hok hd
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hleft | hright
      · subst hroot; exact ⟨x, hd⟩
      · exact ihl hokl (c + 1) yl hyl p hleft
      · exact ihr hokr _ yr hyr p hright
end Nock.Verb
