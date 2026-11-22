-- Prove2me | solution 1 for Nock.evalGPaper_succeeds_below_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:22.004612+00:00
-- url     : https://prove2.me/submissions/8eaa6ec6-d7e4-4fd9-8496-08dedcd5501d

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
    evalGPaper 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) := by
  refine ⟨by decide, by decide, by decide⟩
end Nock
