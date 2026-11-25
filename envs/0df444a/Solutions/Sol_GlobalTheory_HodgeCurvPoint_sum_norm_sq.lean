-- Prove2me | solution 1 for GlobalTheory.HodgeCurvPoint.sum_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:36.185838+00:00
-- url     : https://prove2.me/submissions/6e126bc1-bb30-425e-991a-8dc9eea4fc58

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
theorem _root_.solution (v : Fin g → ℂ) : ∑ j, ‖v j‖ ^ 2 =
    (fun j => (v j).re) ⬝ᵥ (fun j => (v j).re) + (fun j => (v j).im) ⬝ᵥ (fun j => (v j).im) := by
  simp only [dotProduct, ← Finset.sum_add_distrib, Complex.sq_norm, Complex.normSq_apply]
end GlobalTheory.HodgeCurvPoint
