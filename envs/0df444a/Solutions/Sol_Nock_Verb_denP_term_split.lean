-- Prove2me | solution 1 for Nock.Verb.denP_term_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:19.784734+00:00
-- url     : https://prove2.me/submissions/2737d6ee-c9e5-44fe-b44e-b44730aed66e

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_denP_terminal_val

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l r : Verb} {f : Nat} {x : Noun}
    (htl : isTerminal l = true) (htr : isTerminal r = true)
    (h : denP (f + 1) (Verb.node .null l r) = some x) :
    denP f l = some l.noun ∧ denP f r = some r.noun := by
  simp only [denP] at h
  cases hl : denP f l with
  | none => rw [hl] at h; simp at h
  | some yl =>
      cases hr : denP f r with
      | none => rw [hl, hr] at h; simp at h
      | some yr =>
          refine ⟨?_, ?_⟩
          · rw [denP_terminal_val htl hl]
          · rw [denP_terminal_val htr hr]
end Nock.Verb
