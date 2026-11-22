-- Prove2me | solution 1 for Nock.Verb.runTrace_adjacent_nockCheck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:55.658806+00:00
-- url     : https://prove2.me/submissions/628a6416-a9a1-44d4-b5c4-f3d697b6aa2b

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
public import Theorems.Thm_Nock_Verb_runTrace_traceOf
public import Theorems.Thm_Nock_Verb_adjNockCheck_of_consistent

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) : AdjNockCheck T :=
  adjNockCheck_of_consistent T (runTrace_traceOf h).2
end Nock.Verb
