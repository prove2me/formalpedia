-- Prove2me | solution 1 for Nock.Verb.editOk_editN_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:03.312023+00:00
-- url     : https://prove2.me/submissions/d766b303-4401-4983-bb6b-e6e553f68d4c

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
theorem _root_.solution {l r} : editOk (.node .edit l r) = (!Verb.isPending r && editOk l && editOk
  r) := rfl
end Nock.Verb
