-- Prove2me | solution 1 for Nock.Verb.inDomain_star_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:12.137371+00:00
-- url     : https://prove2.me/submissions/a7959384-7ff5-4071-8f01-84cb8a9463ad

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {L I n2 : Verb} {rb : Action}
    (hL : isTerminal L = true) (hrb : rb.isNull = true) (hI : isTerminal I = true)
    (hn2 : isTerminal n2 = true) (hhead : opHeadOk I = true) :
    inDomain (Verb.node .star L (Verb.node rb I n2)) = true := by
  simp [inDomain, inOpcodeDomain, hL, hrb, hI, hn2, hhead]
end Nock.Verb
