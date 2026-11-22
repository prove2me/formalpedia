-- Prove2me | solution 1 for Nock.Verb.Den_slot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:14.939794+00:00
-- url     : https://prove2.me/submissions/62fa6efa-689e-410f-ab48-48d5e531a8a9

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_pair

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l r x} : Den (.node .slot l r) x ↔
    ∃ ax b, Den l (.atom ax) ∧ Den r b ∧ Noun.slot ax b = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      split at h
      · rename_i ax b hl hr
        exact ⟨ax, b, ⟨f, hl⟩, ⟨f, hr⟩, h⟩
      · simp at h
  · rintro ⟨ax, b, hl, hr, hs⟩
    obtain ⟨f, hl, hr⟩ := den_pair hl hr
    exact ⟨f + 1, by simp only [den, hl, hr]; exact hs⟩
end Nock.Verb
