-- Prove2me | solution 1 for GlobalTheory.HodgeCurvPoint.re_form_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:31.711631+00:00
-- url     : https://prove2.me/submissions/a2f85a66-a187-45af-8630-d5de337fa687

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
theorem _root_.solution (M : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℂ) :
    (form (M.map ofReal) v v).re = (fun j => (v j).re) ⬝ᵥ M *ᵥ (fun j => (v j).re) +
      (fun j => (v j).im) ⬝ᵥ M *ᵥ (fun j => (v j).im) := by
  simp only [form_eq_sum, dotProduct, mulVec, Finset.mul_sum, re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.map_apply, mul_re, mul_im, conj_re, conj_im]; ring
end GlobalTheory.HodgeCurvPoint
