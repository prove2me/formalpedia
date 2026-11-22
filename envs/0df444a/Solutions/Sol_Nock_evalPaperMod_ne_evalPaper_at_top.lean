-- Prove2me | solution 1 for Nock.evalPaperMod_ne_evalPaper_at_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:53.978077+00:00
-- url     : https://prove2.me/submissions/ab0f3183-4374-412d-a4bb-7fcf1f08ca47

module
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution :
    evalPaperMod 3 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 2)))
      ≠ evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 2))) := by
  decide
end Nock
