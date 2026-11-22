-- Prove2me | solution 1 for Nock.bridge_nonvacuous_at_prime_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:07.927801+00:00
-- url     : https://prove2.me/submissions/c653360e-b04f-45d4-9029-76163169bac0

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
public import Theorems.Thm_Nock_paper_field_bridge

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution :
    (∃ n, Verb.runProgram n (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4)) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3))) = some (.atom 4) ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      FieldEmbedding.evalFBy 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalN 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3))) = some (.atom 4) ∧
      FieldEmbedding.BoundedBy 5 (.atom 4) :=
  paper_field_bridge 5 (by norm_num) (by norm_num [FieldEmbedding.BoundedBy]) (by norm_num [FieldEmbedding.BoundedBy]) (by decide)
end Nock
