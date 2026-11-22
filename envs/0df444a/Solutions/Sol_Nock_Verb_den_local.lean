-- Prove2me | solution 1 for Nock.Verb.den_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:56.055028+00:00
-- url     : https://prove2.me/submissions/dfdf4b1b-7a8c-427a-a89d-54fce2e4e06c

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_local_opReady
public import Theorems.Thm_Nock_Verb_den_local_opcode

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {sub r₀ x} (hd : inDomain sub = true) (hr : reduce sub = some r₀) :
    (Den sub x ↔ Den r₀ x) := by
  rw [inDomain, Bool.or_eq_true] at hd
  rcases hd with h | h
  · exact den_local_opcode h hr
  · exact den_local_opReady h hr
end Nock.Verb
