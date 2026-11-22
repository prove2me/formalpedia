-- Prove2me | solution 1 for Nock.Verb.denP_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:47.037695+00:00
-- url     : https://prove2.me/submissions/745277c3-c38d-417b-b3ae-9494da874d6d

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_mono

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l r a b} (hl : DenP l a) (hr : DenP r b) :
    ∃ f, denP f l = some a ∧ denP f r = some b := by
  obtain ⟨fl, hl⟩ := hl; obtain ⟨fr, hr⟩ := hr
  exact ⟨max fl fr, denP_mono (Nat.le_max_left _ _) hl, denP_mono (Nat.le_max_right _ _) hr⟩
end Nock.Verb
