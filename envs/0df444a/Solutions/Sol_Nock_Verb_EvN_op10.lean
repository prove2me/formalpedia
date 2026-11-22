-- Prove2me | solution 1 for Nock.Verb.EvN_op10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:27.085193+00:00
-- url     : https://prove2.me/submissions/39c20e24-ca1b-491f-8044-a444c724f485

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
theorem _root_.solution {subj tail x} : Ev subj (.cell (.atom 10) tail) x ↔
    ∃ ax c d new old, tail = .cell (.cell (.atom ax) c) d ∧
      Ev subj c new ∧ Ev subj d old ∧ Noun.edit ax new old = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      split at h
      · rename_i ax c d
        split at h
        · rename_i new old hnew hold
          exact ⟨ax, c, d, new, old, rfl, ⟨f, hnew⟩, ⟨f, hold⟩, h⟩
        · simp at h
      · simp at h
  · rintro ⟨ax, c, d, new, old, rfl, hnew, hold, he⟩
    obtain ⟨f, hnew, hold⟩ := ev2 hnew hold
    refine ⟨f + 1, ?_⟩
    rw [evalN, hnew, hold]
    exact he
end Nock.Verb
