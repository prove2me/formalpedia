-- Prove2me | solution 1 for GlobalTheory.HodgeCurvPoint.posSemidef_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:09.522743+00:00
-- url     : https://prove2.me/submissions/52e17bb4-cf12-41d8-abae-612d2c914326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_isHermitian_map
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_form_map_self
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
theorem _root_.solution {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm)
    (h : ∀ x, 0 ≤ x ⬝ᵥ M *ᵥ x) : (M.map ofReal).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_map hM, fun x => ?_⟩
  have e : star x ⬝ᵥ (M.map ofReal) *ᵥ x = form (M.map ofReal) (star x) (star x) := by
    simp [form]
  rw [e, form_map_self hM]
  exact_mod_cast add_nonneg (h _) (h _)
end GlobalTheory.HodgeCurvPoint
