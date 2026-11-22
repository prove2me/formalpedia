-- Prove2me | solution 1 for Nock.Verb.DenP_terminal_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:07.436407+00:00
-- url     : https://prove2.me/submissions/425700bc-23f6-4f1a-bddd-46fa1131ab0e

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_terminal
public import Theorems.Thm_Nock_Verb_denP_det

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v x} (ht : isTerminal v = true) : DenP v x ↔ x = v.noun := by
  constructor
  · intro hd; exact denP_det hd ⟨v.noun.size, denP_terminal v v.noun.size ht (Nat.le_refl _)⟩
  · rintro rfl; exact ⟨v.noun.size, denP_terminal v v.noun.size ht (Nat.le_refl _)⟩
end Nock.Verb
