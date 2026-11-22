-- Prove2me | solution 1 for Nock.Verb.consistent_of_consistentROM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:31.37307+00:00
-- url     : https://prove2.me/submissions/71083fe0-85aa-46d7-a4dc-4cb8dd76ba40

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_step_of_stepROM

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution : ∀ (T : List Verb), ConsistentR StepROM T → Consistent T
  | [],            _ => trivial
  | [_],           _ => trivial
  | _ :: _ :: rest, h => ⟨step_of_stepROM h.1, solution (_ :: rest) h.2⟩
end Nock.Verb
