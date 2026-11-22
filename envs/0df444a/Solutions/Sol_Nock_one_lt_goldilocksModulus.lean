-- Prove2me | solution 1 for Nock.one_lt_goldilocksModulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:04.275112+00:00
-- url     : https://prove2.me/submissions/af7727be-c62f-4dae-be9a-640caf83deff

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution : 1 < goldilocksModulus := by
  norm_num [goldilocksModulus]
end Nock
