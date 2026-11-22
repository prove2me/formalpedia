-- Prove2me | solution 1 for Nock.Verb.runTrace_traceOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:14.973838+00:00
-- url     : https://prove2.me/submissions/ac7fe9c0-ec77-4838-9c62-68c96cfafb46

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
public import Theorems.Thm_Nock_Verb_runTrace_spec

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) : TraceOf v T := (runTrace_spec fuel v T h).1
end Nock.Verb
