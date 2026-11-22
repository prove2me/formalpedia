-- Prove2me | solution 1 for Nock.Verb.Rel.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:19.987702+00:00
-- url     : https://prove2.me/submissions/681eb9f1-8925-4681-baf4-6ac2b082e79e

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
namespace Rel
theorem _root_.solution : ∀ v, Rel v v
  | .leaf _   => .leaf
  | .node _ l r => .cong (solution l) (solution r)
end Rel
end Nock.Verb
