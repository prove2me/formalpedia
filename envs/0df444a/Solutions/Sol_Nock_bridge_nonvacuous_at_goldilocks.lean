-- Prove2me | solution 1 for Nock.bridge_nonvacuous_at_goldilocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:18.288339+00:00
-- url     : https://prove2.me/submissions/abb711ef-7a75-431a-9a98-d9cb8a132ba4

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
public import Theorems.Thm_Nock_paper_field_bridge
public import Theorems.Thm_Nock_one_lt_goldilocksModulus

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution :
    (∃ n, Verb.runProgram n (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
        = some (.atom 43)) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      evalPaperMod goldilocksModulus 5 (.atom 0)
          (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      FieldEmbedding.evalFBy goldilocksModulus 5 (.atom 0)
          (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      evalN 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      FieldEmbedding.BoundedBy goldilocksModulus (.atom 43) :=
  paper_field_bridge goldilocksModulus one_lt_goldilocksModulus
    (by norm_num [goldilocksModulus, FieldEmbedding.BoundedBy]) (by norm_num [goldilocksModulus, FieldEmbedding.BoundedBy])
    (by have hgm : goldilocksModulus = 18446744069414584321 := by norm_num [goldilocksModulus]
        rw [hgm]; decide)
end Nock
