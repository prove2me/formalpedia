-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CellSumProof.measurable_hits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:22:54.244802+00:00
-- url     : https://prove2.me/submissions/b3e2e69f-5ebc-4560-842f-4faa83df0aa1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CellSumOfCntBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CellSumProof
namespace GlobalTheory.CompanionTheory.CellSumProof
theorem _root_.solution (X : Ctx) {S : Set X.G} (hS : MeasurableSet S) :
    Measurable (hits X S) := by
  unfold hits
  refine Measurable.ennreal_tsum fun γ => ?_
  exact (measurable_one.indicator hS).comp (measurable_const_mul (γ : X.G))
end GlobalTheory.CompanionTheory.CellSumProof
