-- Prove2me | solution 1 for GlobalTheory.HyperboloidPolar.hypAmb_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:47.123341+00:00
-- url     : https://prove2.me/submissions/7c7ed923-1bcd-4919-9d22-3b7e0c7506a6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TransW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasurePolarForm
import Theorems.Thm_GlobalTheory_HyperboloidPolar_opVec_inWb
import Theorems.Thm_GlobalTheory_HyperboloidPolar_opVec_opCo
import Theorems.Thm_GlobalTheory_HyperboloidPolar_inWb_uwb
import Theorems.Thm_GlobalTheory_HyperboloidPolar_continuous_opVec
import Theorems.Thm_GlobalTheory_HyperboloidPolar_continuous_opCo
import Theorems.Thm_PI_RhsWLim_W_coneForm_of
import Theorems.Thm_PI_RhsWLim_W_coneVol
import Theorems.Thm_PI_RhsWLim_W_hypInv_of
import Theorems.Thm_PI_RhsWLim_W_hypTh
import Theorems.Thm_PI_RhsWLim_W_lebInvB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HyperboloidPolar
open PI.RhsWLim PI.RhsWLim.W
variable {k r : ℕ}
namespace GlobalTheory.HyperboloidPolar
theorem _root_.solution (hk : 1 ≤ k) {T' : ℝ} (hT' : 0 < T') {s : Mat k r} (hs : s ∈ UWb k r) :
    (hypAmb k r T').map (fun v => s *ᵥ v) = hypAmb k r T' := by
  have hI := hypInv_of lebInvB (coneForm_of hypTh coneVol) k r T' hk hT' s hs
  have hm : Continuous (fun v : Fin (2 * r + k + 1) → ℂ => s *ᵥ v) :=
    continuous_const.matrix_mulVec continuous_id
  have hA : Continuous (opAct k r s) := continuous_opCo.comp (hm.comp continuous_opVec)
  have e : (fun v => s *ᵥ v) ∘ opVec k r = opVec k r ∘ opAct k r s := by
    funext p
    exact (opVec_opCo (inWb_uwb hs (opVec_inWb p))).symm
  rw [hypAmb, Measure.map_map hm.measurable continuous_opVec.measurable, e,
    ← Measure.map_map continuous_opVec.measurable hA.measurable, hI]
end GlobalTheory.HyperboloidPolar
