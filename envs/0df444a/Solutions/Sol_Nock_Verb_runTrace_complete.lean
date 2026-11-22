-- Prove2me | solution 1 for Nock.Verb.runTrace_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:19.77635+00:00
-- url     : https://prove2.me/submissions/204b7488-d948-411d-bb14-97eb6f326e93

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
    (h : runTrace fuel v = some T) : Complete T := (runTrace_spec fuel v T h).2
end Nock.Verb
