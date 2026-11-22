-- Prove2me | solution 1 for Nock.evalGPaper_fails_where_evalPaperMod_wraps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:18.980812+00:00
-- url     : https://prove2.me/submissions/1d403781-0e77-45aa-89f5-d0ff2ca1e648

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
theorem _root_.solution :
    evalGPaper 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4))) = none ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4)))
        = some (.atom 0) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4)))
        = some (.atom 5) := by
  refine ⟨by decide, by decide, by decide⟩
end Nock
