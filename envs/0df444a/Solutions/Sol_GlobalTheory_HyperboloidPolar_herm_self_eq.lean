-- Prove2me | solution 1 for GlobalTheory.HyperboloidPolar.herm_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:05.113298+00:00
-- url     : https://prove2.me/submissions/1b2559a1-2cfc-4625-b5ca-ca53342b89f5

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
import Theorems.Thm_PI_RhsWLim_W_hermHb_self
import Theorems.Thm_PI_RhsWLim_W_herm_wb


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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    herm (Hpk k r) z z = ((-Tz k r z : ℝ) : ℂ) := by
  unfold Tz
  rw [neg_neg, herm_wb _ _ hz, hermHb_self, Complex.ofReal_re]
end GlobalTheory.HyperboloidPolar
