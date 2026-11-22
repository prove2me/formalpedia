-- Prove2me | solution 1 for Nock.Verb.lus_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:25.875241+00:00
-- url     : https://prove2.me/submissions/eaa17372-4db9-4b33-897f-7a51091d1487

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {k : Nat} : Noun.lus (.atom k) = some (.atom (k+1)) := by simp [Noun.lus]
end Nock.Verb
