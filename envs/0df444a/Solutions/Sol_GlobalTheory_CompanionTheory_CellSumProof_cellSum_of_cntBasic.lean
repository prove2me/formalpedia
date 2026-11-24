-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CellSumProof.cellSum_of_cntBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:54:17.676414+00:00
-- url     : https://prove2.me/submissions/c9292a58-50a3-4dd5-9683-8099485f8fb2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CellSumOfCntBasic
import Theorems.Thm_GlobalTheory_CompanionTheory_CellSumProof_cellSum_holds

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
theorem _root_.solution : CntBasic → CellSum := fun _ => cellSum_holds
end GlobalTheory.CompanionTheory.CellSumProof
