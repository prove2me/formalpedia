-- Prove2me | solution 1 for Nock.Verb.den_iff_evalN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:13.717669+00:00
-- url     : https://prove2.me/submissions/dd8cc405-1d48-40e3-b593-85b6f243e9ff

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_mono
public import Theorems.Thm_Nock_Verb_den_program
public import Theorems.Thm_Nock_evalN_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (s f r : Noun) :
    (∃ fuel, den fuel (program s f) = some r) ↔ (∃ fuel, evalN fuel s f = some r) := by
  constructor
  · rintro ⟨fuel, h⟩
    refine ⟨max fuel (max s.size f.size), ?_⟩
    have hm : fuel ≤ max fuel (max s.size f.size) + 1 := by omega
    have hs : s.size ≤ max fuel (max s.size f.size) := by omega
    have hf : f.size ≤ max fuel (max s.size f.size) := by omega
    have := den_mono hm h
    rwa [den_program s f _ hs hf] at this
  · rintro ⟨fuel, h⟩
    refine ⟨max fuel (max s.size f.size) + 1, ?_⟩
    have hm : fuel ≤ max fuel (max s.size f.size) := by omega
    have hs : s.size ≤ max fuel (max s.size f.size) := by omega
    have hf : f.size ≤ max fuel (max s.size f.size) := by omega
    rw [den_program s f _ hs hf]
    exact evalN_mono hm h
end Nock.Verb
