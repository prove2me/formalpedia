-- Prove2me | solution 1 for Nock.FieldEmbedding.embBy_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:22.877044+00:00
-- url     : https://prove2.me/submissions/3c225d91-841a-4438-be2e-19f756a6f572

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
open Nock.FieldEmbedding
namespace Nock.FieldEmbedding
theorem _root_.solution {q n : Nat} : embBy q (.atom n) = .atom (n : ZMod q) := rfl
end Nock.FieldEmbedding
