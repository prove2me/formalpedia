-- Prove2me | solution 1 for GlobalTheory.HyperboloidPolar.inWb_uwb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:25.066382+00:00
-- url     : https://prove2.me/submissions/7315dd40-2c3b-4de6-a9c0-72a230e85383

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
import Theorems.Thm_PI_RhsWLim_W_RI_inWb_emb
import Theorems.Thm_PI_RhsWLim_W_op_uwb_eq_emb


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
theorem _root_.solution {s : Mat k r} (hs : s ∈ UWb k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (s *ᵥ v) := by
  rw [op_uwb_eq_emb hs]
  exact RI.inWb_emb _ hv
end GlobalTheory.HyperboloidPolar
