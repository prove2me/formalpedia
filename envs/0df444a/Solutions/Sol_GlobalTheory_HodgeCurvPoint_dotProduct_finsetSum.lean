-- Prove2me | solution 1 for GlobalTheory.HodgeCurvPoint.dotProduct_finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:35.46829+00:00
-- url     : https://prove2.me/submissions/60433b2a-e862-4760-b381-46a0f9d1cfe7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeCurvPoint
variable {g : ℕ}
namespace GlobalTheory.HodgeCurvPoint
theorem _root_.solution {a : ℕ} (u : Fin g → ℂ) (w : Fin a → Fin g → ℂ) :
    u ⬝ᵥ ∑ i, w i = ∑ i, u ⬝ᵥ w i := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm
end GlobalTheory.HodgeCurvPoint
