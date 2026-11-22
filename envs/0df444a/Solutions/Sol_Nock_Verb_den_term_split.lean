-- Prove2me | solution 1 for Nock.Verb.den_term_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:43.791585+00:00
-- url     : https://prove2.me/submissions/9c02595c-0982-4363-acde-a9c5246008c5

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_den_terminal_val

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l r : Verb} {f : Nat} {x : Noun}
    (htl : isTerminal l = true) (htr : isTerminal r = true)
    (h : den (f + 1) (Verb.node .null l r) = some x) :
    den f l = some l.noun ∧ den f r = some r.noun := by
  simp only [den] at h
  cases hl : den f l with
  | none => rw [hl] at h; simp at h
  | some yl =>
      cases hr : den f r with
      | none => rw [hl, hr] at h; simp at h
      | some yr =>
          refine ⟨?_, ?_⟩
          · rw [den_terminal_val htl hl]
          · rw [den_terminal_val htr hr]
end Nock.Verb
