-- Prove2me | solution 1 for Nock.Verb.editOk_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:42.814853+00:00
-- url     : https://prove2.me/submissions/ca79a303-1297-435f-9a61-5cb3edbaa5f0

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
theorem _root_.solution {l r} : editOk (.node .star l r) = (editOk l && editOk r) := rfl
end Nock.Verb
