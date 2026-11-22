-- Prove2me | solution 1 for Nock.Verb.denP_iff_evalPaper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:39.936615+00:00
-- url     : https://prove2.me/submissions/128f5e10-5308-43b3-8c82-cddaf723bd49

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_mono
public import Theorems.Thm_Nock_Verb_denP_program
public import Theorems.Thm_Nock_evalPaper_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (s f r : Noun) :
    (∃ fuel, denP fuel (program s f) = some r) ↔ (∃ fuel, evalPaper fuel s f = some r) := by
  constructor
  · rintro ⟨fuel, h⟩
    refine ⟨max fuel (max s.size f.size), ?_⟩
    have hm : fuel ≤ max fuel (max s.size f.size) + 1 := by omega
    have hs : s.size ≤ max fuel (max s.size f.size) := by omega
    have hf : f.size ≤ max fuel (max s.size f.size) := by omega
    have := denP_mono hm h
    rwa [denP_program s f _ hs hf] at this
  · rintro ⟨fuel, h⟩
    refine ⟨max fuel (max s.size f.size) + 1, ?_⟩
    have hm : fuel ≤ max fuel (max s.size f.size) := by omega
    have hs : s.size ≤ max fuel (max s.size f.size) := by omega
    have hf : f.size ≤ max fuel (max s.size f.size) := by omega
    rw [denP_program s f _ hs hf]
    exact evalPaper_mono hm h
end Nock.Verb
