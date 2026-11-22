-- Prove2me | solution 1 for Nock.Verb.traceOf_of_traceOfROM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:56.292168+00:00
-- url     : https://prove2.me/submissions/ce5a1251-39a2-4ae8-abac-8c849642b6d4

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_consistent_of_consistentROM

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {F : Verb} {T : List Verb} (h : TraceOfROM F T) : TraceOf F T :=
  ⟨h.1, consistent_of_consistentROM T h.2⟩
end Nock.Verb
