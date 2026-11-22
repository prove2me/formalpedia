-- Prove2me | solution 1 for Nock.Verb.runProgram_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:50.217507+00:00
-- url     : https://prove2.me/submissions/997a8f32-2489-4979-9d3a-e9bb90d7731d

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_iff_evalN
public import Theorems.Thm_Nock_Verb_editOk_program
public import Theorems.Thm_Nock_Verb_run_sound

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {s f r : Noun} {fuel : Nat}
    (h : runProgram fuel s f = some r) : ∃ fuel', evalN fuel' s f = some r := by
  have : ∃ f', den f' (program s f) = some r := run_sound fuel (editOk_program s f) h
  exact (den_iff_evalN s f r).1 this
end Nock.Verb
