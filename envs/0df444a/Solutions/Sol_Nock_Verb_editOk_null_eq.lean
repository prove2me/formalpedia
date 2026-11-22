-- Prove2me | solution 1 for Nock.Verb.editOk_null_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:11.212497+00:00
-- url     : https://prove2.me/submissions/54d2111c-e537-4ec7-a64d-5c7014e87141

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
theorem _root_.solution {l r} : editOk (.node .null l r) = (editOk l && editOk r) := rfl
end Nock.Verb
