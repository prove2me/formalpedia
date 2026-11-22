-- Prove2me | solution 1 for Nock.Verb.Den_terminal_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:59.79682+00:00
-- url     : https://prove2.me/submissions/c8bba426-a4de-4e51-b7fd-9b0d60c7687d

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_terminal
public import Theorems.Thm_Nock_Verb_den_det

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v x} (ht : isTerminal v = true) : Den v x ↔ x = v.noun := by
  constructor
  · intro hd; exact den_det hd ⟨v.noun.size, den_terminal v v.noun.size ht (Nat.le_refl _)⟩
  · rintro rfl; exact ⟨v.noun.size, den_terminal v v.noun.size ht (Nat.le_refl _)⟩
end Nock.Verb
