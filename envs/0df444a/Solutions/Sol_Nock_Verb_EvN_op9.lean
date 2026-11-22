-- Prove2me | solution 1 for Nock.Verb.EvN_op9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:34.1158+00:00
-- url     : https://prove2.me/submissions/1496efb3-45fd-4a44-983d-7eb6acd37b39

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
theorem _root_.solution {subj tail x} : Ev subj (.cell (.atom 9) tail) x ↔
    ∃ ax c core arm, tail = .cell (.atom ax) c ∧ Ev subj c core ∧
      Noun.slot ax core = some arm ∧ Ev core arm x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom => simp at h
      | cell head c =>
        cases head with
        | cell => simp at h
        | atom ax =>
          simp only at h
          cases hcore : evalN f subj c with
          | none => rw [hcore] at h; simp at h
          | some core =>
            rw [hcore] at h
            simp only at h
            cases hslot : Noun.slot ax core with
            | none => rw [hslot] at h; simp at h
            | some arm =>
              rw [hslot] at h
              exact ⟨ax, c, core, arm, rfl, ⟨f, hcore⟩, hslot, ⟨f, h⟩⟩
  · rintro ⟨ax, c, core, arm, rfl, hcore, hslot, hx⟩
    obtain ⟨f, hcore, hx⟩ := ev2 hcore hx
    refine ⟨f + 1, ?_⟩
    rw [evalN]; simp only [hcore, hslot]; exact hx
end Nock.Verb
