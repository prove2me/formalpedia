-- Prove2me | solution 1 for Nock.Verb.finite_of_valid_or_invalid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:54.991976+00:00
-- url     : https://prove2.me/submissions/2fd17871-a828-4317-a55b-80f7c62ff9c9

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_finite_of_valid
public import Theorems.Thm_Nock_Verb_finite_of_invalid

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {F : Verb} (h : Valid F ∨ Invalid F) : Finite F :=
  h.elim finite_of_valid finite_of_invalid
end Nock.Verb
