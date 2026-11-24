-- Prove2me | solution 1 for GlobalTheory.JR.Step.blocks_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:11:11.304601+00:00
-- url     : https://prove2.me/submissions/42d75809-250a-48a6-8f58-e10f17031a75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
variable {r : ℕ} {k : Type} [CommRing k]
namespace GlobalTheory.JR.Step
theorem _root_.solution (Y : Gl r k) : blocks (full Y) = Y := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc]
  · ext i
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  · ext i
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  · simp [blocks, full, finSumFinEquiv_symm_last]
end GlobalTheory.JR.Step
