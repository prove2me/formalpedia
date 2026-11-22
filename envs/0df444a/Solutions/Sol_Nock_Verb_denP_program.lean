-- Prove2me | solution 1 for Nock.Verb.denP_program
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:05.838809+00:00
-- url     : https://prove2.me/submissions/0e7be3c6-86d2-4ff5-a1df-1679625ece5f

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_ofNoun

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (s f : Noun) (fuel : Nat) (hs : s.size ≤ fuel) (hf : f.size ≤ fuel) :
    denP (fuel + 1) (program s f) = evalPaper fuel s f := by
  simp only [program, denP, denP_ofNoun s fuel hs, denP_ofNoun f fuel hf]
end Nock.Verb
