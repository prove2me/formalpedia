-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ConvTest.cvTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:56:35.558374+00:00
-- url     : https://prove2.me/submissions/9c9cc062-04dd-450a-aa48-2563b11aa81d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableReflect
import Theorems.Thm_GlobalTheory_CompanionTheory_ConvTest_support_cv_subset
import Theorems.Thm_GlobalTheory_CompanionTheory_ConvTest_continuous_cv
import Theorems.Thm_GlobalTheory_CompanionTheory_ConvTest_norm_cv_le

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
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ConvTest
variable (X : Ctx)
namespace GlobalTheory.CompanionTheory.ConvTest
theorem _root_.solution : CvTest := by
  intro X φ ψ hφ hψ
  have hsupp := support_cv_subset X φ ψ
  refine ⟨⟨continuous_cv X hφ hψ, ?_⟩, hsupp, fun B hB y => norm_cv_le X hψ B hB y⟩
  have hK : IsCompact (tsupport φ * tsupport ψ) := IsCompact.mul hφ.2 hψ.2
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  exact hy (hsupp hne)
end GlobalTheory.CompanionTheory.ConvTest
