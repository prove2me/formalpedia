-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelCount.cntBasic_of_kerBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:41.934822+00:00
-- url     : https://prove2.me/submissions/9ad188d7-4029-4fa0-976a-308605549d85

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CntBasicOfKerBasic
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelCount_cnt_ne_top
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelCount_cnt_mul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelCount_cnt_mono
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelCount_enorm_le_indicator

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
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelCount
namespace GlobalTheory.CompanionTheory.KernelCount
theorem _root_.solution (h : KerBasic) : CntBasic := by
  intro X
  refine ⟨fun Ω hΩ x => cnt_ne_top X Ω hΩ x, fun Ω γ hγ x => cnt_mul_left X Ω γ hγ x,
    fun Ω Ω' hs x => cnt_mono X hs x, fun φ B hφ hB x => ?_⟩
  obtain ⟨-, -, -, -, -, hk⟩ := h X φ hφ
  refine (hk x x).trans ?_
  unfold cnt
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun γ => enorm_le_indicator φ B hB _
end GlobalTheory.CompanionTheory.KernelCount
