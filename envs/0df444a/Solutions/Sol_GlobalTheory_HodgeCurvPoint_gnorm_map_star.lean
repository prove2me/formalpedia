-- Prove2me | solution 1 for GlobalTheory.HodgeCurvPoint.gnorm_map_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:39.293043+00:00
-- url     : https://prove2.me/submissions/1053bdff-139b-4aa4-b81d-3bd1a4693f42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_re_form_map
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
theorem _root_.solution (M : Matrix (Fin g) (Fin g) ℝ) (u : Fin g → ℂ) :
    gnorm (M.map ofReal) (star u) = gnorm (M.map ofReal) u := by
  have e1 : (fun j => (star u j).re) = fun j => (u j).re := by ext j; simp
  have e2 : (fun j => (star u j).im) = -fun j => (u j).im := by ext j; simp
  rw [gnorm, gnorm, re_form_map, re_form_map, e1, e2, mulVec_neg, neg_dotProduct, dotProduct_neg,
    neg_neg]
end GlobalTheory.HodgeCurvPoint
