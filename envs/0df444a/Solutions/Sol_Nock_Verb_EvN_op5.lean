-- Prove2me | solution 1 for Nock.Verb.EvN_op5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:26.055883+00:00
-- url     : https://prove2.me/submissions/50260ca7-821b-4e6d-b4d9-e64c44b2c926

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
theorem _root_.solution {subj tail x} : Ev subj (.cell (.atom 5) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev subj hc sc ∧ x = Noun.tis sb sc := by
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
          exact ⟨hb, hc, sb, sc, rfl, ⟨f, hsb⟩, ⟨f, hsc⟩, (Option.some.inj h).symm⟩
        · simp at h
  · rintro ⟨hb, hc, sb, sc, rfl, hsb, hsc, rfl⟩
    obtain ⟨f, hsb, hsc⟩ := ev2 hsb hsc
    exact ⟨f + 1, by simp only [evalN, hsb, hsc]⟩
end Nock.Verb
