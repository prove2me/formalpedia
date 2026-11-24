-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Schur.eLpNorm_two_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:35:11.240358+00:00
-- url     : https://prove2.me/submissions/ca0804db-9c62-4065-9809-eb6c684d1781

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchurOpOfSchurL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Schur
open PositivityTheory.Rg.BcB.E1
variable {α : Type} [MeasurableSpace α] {ν : Measure α}
namespace GlobalTheory.CompanionTheory.Schur
theorem _root_.solution (f : α → ℂ) : eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)
  simpa [ENNReal.rpow_ofNat] using h
end GlobalTheory.CompanionTheory.Schur
