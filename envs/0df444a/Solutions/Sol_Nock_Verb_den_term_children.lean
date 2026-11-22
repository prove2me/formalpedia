-- Prove2me | solution 1 for Nock.Verb.den_term_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:41.384648+00:00
-- url     : https://prove2.me/submissions/9404bda6-cb42-4351-903b-c75e288c5262

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_den_children_F
public import Theorems.Thm_Nock_Verb_den_terminal_val

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den F (Verb.node a l r) = some x)
    (htl : isTerminal l = true) (htr : isTerminal r = true) :
    den F l = some l.noun ∧ den F r = some r.noun := by
  obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := den_children_F hok h
  rw [den_terminal_val htl hyl] at hyl
  rw [den_terminal_val htr hyr] at hyr
  exact ⟨hyl, hyr⟩
end Nock.Verb
