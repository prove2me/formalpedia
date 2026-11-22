-- Prove2me | solution 1 for Nock.Verb.denP_term_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:28.19903+00:00
-- url     : https://prove2.me/submissions/5eaf5a49-d3c9-4236-b2e7-2e0588a986fd

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_denP_children_F
public import Theorems.Thm_Nock_Verb_denP_terminal_val

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP F (Verb.node a l r) = some x)
    (htl : isTerminal l = true) (htr : isTerminal r = true) :
    denP F l = some l.noun ∧ denP F r = some r.noun := by
  obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := denP_children_F hok h
  rw [denP_terminal_val htl hyl] at hyl
  rw [denP_terminal_val htr hyr] at hyr
  exact ⟨hyl, hyr⟩
end Nock.Verb
