-- Prove2me | solution 1 for Nock.Verb.EvN_op2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:46.291242+00:00
-- url     : https://prove2.me/submissions/63abcf83-8ef1-4c79-b11e-54c47aabab0c

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_ev3

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj tail x} : Ev subj (.cell (.atom 2) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev subj hc sc ∧ Ev sb sc x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom => simp at h
      | cell hb hc =>
        simp only at h
        split at h
        · rename_i sb sc hsb hsc
          exact ⟨hb, hc, sb, sc, rfl, ⟨f, hsb⟩, ⟨f, hsc⟩, ⟨f, h⟩⟩
        · simp at h
  · rintro ⟨hb, hc, sb, sc, rfl, hsb, hsc, hx⟩
    obtain ⟨f, hsb, hsc, hx⟩ := ev3 hsb hsc hx
    exact ⟨f + 1, by simp only [evalN, hsb, hsc]; exact hx⟩
end Nock.Verb
