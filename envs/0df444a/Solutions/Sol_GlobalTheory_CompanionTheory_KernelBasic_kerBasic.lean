-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelBasic.kerBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:11:57.064934+00:00
-- url     : https://prove2.me/submissions/2cf70044-b1a0-4fc3-9827-77110c71a8dd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOfCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_support_finite
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_continuous_ker
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_ker_mul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_ker_mul_right
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_tst_adj
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_ker_adj
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_enorm_ker_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelBasic
namespace GlobalTheory.CompanionTheory.KernelBasic
theorem _root_.solution : KerBasic := by
  intro X φ hφ
  exact ⟨support_finite X hφ.2, continuous_ker X hφ,
    fun γ hγ x y => ⟨ker_mul_left X φ hγ x y, ker_mul_right X φ hγ x y⟩,
    tst_adj X hφ, ker_adj X hφ.2, enorm_ker_le X hφ.2⟩
end GlobalTheory.CompanionTheory.KernelBasic
