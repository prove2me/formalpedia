-- Prove2me | solution 1 for Nock.Verb.eval_crash_iff_invalid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:35.758348+00:00
-- url     : https://prove2.me/submissions/ef9871b0-0d8f-4eae-8107-ec670333a3d9

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_eval_crash_invalid
public import Theorems.Thm_Nock_Verb_eval_crash_complete

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {v : Verb} : (∃ n, eval n v = .crash) ↔ Invalid v :=
  ⟨fun ⟨_, h⟩ => eval_crash_invalid h, eval_crash_complete⟩
end Nock.Verb
