-- Prove2me | solution 1 for Nock.Verb.den_program
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:48.0628+00:00
-- url     : https://prove2.me/submissions/b2da865c-d298-4820-9795-98aa3f806ff8

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_ofNoun

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (s f : Noun) (fuel : Nat) (hs : s.size ≤ fuel) (hf : f.size ≤ fuel) :
    den (fuel + 1) (program s f) = evalN fuel s f := by
  simp only [program, den, den_ofNoun s fuel hs, den_ofNoun f fuel hf]
end Nock.Verb
