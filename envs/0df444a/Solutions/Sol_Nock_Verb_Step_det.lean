-- Prove2me | solution 1 for Nock.Verb.Step.det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:18.104826+00:00
-- url     : https://prove2.me/submissions/08a1af67-b2df-4fd5-90a3-fd79ca66f3f2

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
namespace Step
theorem _root_.solution {a b b' : Verb} (h : Step a b) (h' : Step a b') : b = b' :=
  Option.some.inj (h.symm.trans h')
end Step
end Nock.Verb
