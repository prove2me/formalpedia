-- Prove2me | solution 1 for Nock.Verb.selStep_multivalued_without_strictness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:02.250973+00:00
-- url     : https://prove2.me/submissions/0f6a20b4-b779-4fca-b3a1-63823ac22bc2

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution :
    ∃ (a b b' : Verb), b ≠ b' ∧ SelStep emptyLt a b ∧ SelStep emptyLt a b' := by
  refine ⟨twoRedex, replaceAt 1 twoRedex (.leaf 5), replaceAt 3 twoRedex (.leaf 5), by decide,
    ⟨1, _, .leaf 5, ⟨⟨_, rfl, rfl⟩, fun _ _ hf => hf⟩, rfl, by decide, rfl, rfl⟩,
    ⟨3, _, .leaf 5, ⟨⟨_, rfl, rfl⟩, fun _ _ hf => hf⟩, rfl, by decide, rfl, rfl⟩⟩
end Nock.Verb
