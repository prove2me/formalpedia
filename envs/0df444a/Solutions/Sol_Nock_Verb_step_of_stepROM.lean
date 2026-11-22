-- Prove2me | solution 1 for Nock.Verb.step_of_stepROM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:05.652312+00:00
-- url     : https://prove2.me/submissions/c117f9ad-f267-4a4c-831b-16da8b773bc6

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_next_of_nextROM


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {a b : Verb} (h : StepROM a b) : Step a b := next_of_nextROM h
end Nock.Verb
