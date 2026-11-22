-- Prove2me | solution 1 for Nock.Verb.EvN_op7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:00.418356+00:00
-- url     : https://prove2.me/submissions/6bc4ca08-0904-489a-8c6e-b0564c824491

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_ev2

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj tail x} : Ev subj (.cell (.atom 7) tail) x ↔
    ∃ hb hc sb, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev sb hc x := by
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
        cases hsb : evalN f subj hb with
        | none => rw [hsb] at h; simp at h
        | some sb => rw [hsb] at h; exact ⟨hb, hc, sb, rfl, ⟨f, hsb⟩, ⟨f, h⟩⟩
  · rintro ⟨hb, hc, sb, rfl, hsb, hx⟩
    obtain ⟨f, hsb, hx⟩ := ev2 hsb hx
    exact ⟨f + 1, by simp only [evalN, hsb]; exact hx⟩
end Nock.Verb
