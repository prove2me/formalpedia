-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchurKernel.lintegral_enorm_rpow_two_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:35:12.630816+00:00
-- url     : https://prove2.me/submissions/21b6c6f8-63d6-4a83-8d60-4ce39bf1eb3b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralEnormRpowTwoNeTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchurKernel
namespace GlobalTheory.CompanionTheory.SchurKernel
theorem _root_.solution {α : Type} [MeasurableSpace α] {ν : Measure α} {g : α → ℂ}
    (hg : MemLp g 2 ν) : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂ν ≠ ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num) (by norm_num)
    hg.eLpNorm_lt_top
  simpa using h.ne
end GlobalTheory.CompanionTheory.SchurKernel
