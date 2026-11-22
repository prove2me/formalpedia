-- Prove2me | solution 1 for Nock.Verb.EvP_op9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:55.846386+00:00
-- url     : https://prove2.me/submissions/609dea6a-3868-467e-bf93-6a073b7dff3c

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_ev2P

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj tail x} : EvP subj (.cell (.atom 9) tail) x ↔
    ∃ ax c core arm, tail = .cell (.atom ax) c ∧ EvP subj c core ∧
      Noun.slot ax core = some arm ∧ EvP core arm x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom => simp at h
      | cell head c =>
        cases head with
        | cell => simp at h
        | atom ax =>
          simp only at h
          cases hcore : evalPaper f subj c with
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
    obtain ⟨f, hcore, hx⟩ := ev2P hcore hx
    refine ⟨f + 1, ?_⟩
    rw [evalPaper]; simp only [hcore, hslot]; exact hx
end Nock.Verb
