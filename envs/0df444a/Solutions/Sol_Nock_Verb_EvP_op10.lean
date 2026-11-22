-- Prove2me | solution 1 for Nock.Verb.EvP_op10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:57.519853+00:00
-- url     : https://prove2.me/submissions/6a91ced8-9ba0-4920-840e-55fd5065d8a4

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
theorem _root_.solution {subj tail x} : EvP subj (.cell (.atom 10) tail) x ↔
    ∃ ax c d new old, tail = .cell (.cell (.atom ax) c) d ∧
      EvP subj c new ∧ EvP subj d old ∧ Noun.edit ax new old = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      split at h
      · rename_i ax c d
        split at h
        · rename_i new old hnew hold
          exact ⟨ax, c, d, new, old, rfl, ⟨f, hnew⟩, ⟨f, hold⟩, h⟩
        · simp at h
      · simp at h
  · rintro ⟨ax, c, d, new, old, rfl, hnew, hold, he⟩
    obtain ⟨f, hnew, hold⟩ := ev2P hnew hold
    refine ⟨f + 1, ?_⟩
    rw [evalPaper, hnew, hold]
    exact he
end Nock.Verb
