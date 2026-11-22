-- Prove2me | solution 1 for Nock.Verb.runTrace_adjNockCheckB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:29.685912+00:00
-- url     : https://prove2.me/submissions/48a9f54e-6747-4c9f-a3c4-259aef58011a

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
public import Theorems.Thm_Nock_Verb_adjNockCheckB_iff
public import Theorems.Thm_Nock_Verb_runTrace_adjacent_nockCheck

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) : adjNockCheckB T = true :=
  (adjNockCheckB_iff T).mpr (runTrace_adjacent_nockCheck h)
end Nock.Verb
