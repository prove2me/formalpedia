-- Prove2me | solution 1 for GlobalTheory.HyperboloidPolar.herm_opVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:01.974887+00:00
-- url     : https://prove2.me/submissions/2cf11af9-e046-487c-831e-00059a28c621

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
import Theorems.Thm_GlobalTheory_HyperboloidPolar_wbPart_opVec
import Theorems.Thm_PI_RhsWLim_W_herm_wb
import Theorems.Thm_PI_RhsWLim_W_qf_eq


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
theorem _root_.solution (p : (Fin k → ℂ) × ℂ) :
    herm (Hpk k r) (opVec k r p) (opVec k r p) = (qf k p : ℂ) := by
  rw [herm_wb _ _ (opVec_inWb p), wbPart_opVec, qf_eq]
  rfl
end GlobalTheory.HyperboloidPolar
