-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KerSquare.kernel_rows_columns_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:06:59.615847+00:00
-- url     : https://prove2.me/submissions/1e20b3ec-3e3e-4474-8049-e3cc8c05e63b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelRowsColumnsSquareIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_KerSquare_memLp_column
import Theorems.Thm_GlobalTheory_CompanionTheory_KerSquare_memLp_row

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerSquare
namespace GlobalTheory.CompanionTheory.KerSquare
theorem _root_.solution : KerBasic → CntBasic → ColSq → KernelL2RowsColumns := fun hK hC hS X φ hφ =>
  ⟨memLp_column hK hC hS X φ hφ, memLp_row hK hC hS X φ hφ⟩
end GlobalTheory.CompanionTheory.KerSquare
