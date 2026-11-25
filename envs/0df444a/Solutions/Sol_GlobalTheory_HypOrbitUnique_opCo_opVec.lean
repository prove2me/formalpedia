-- Prove2me | solution 1 for GlobalTheory.HypOrbitUnique.opCo_opVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:51.25541+00:00
-- url     : https://prove2.me/submissions/aaae631c-3c03-4f40-b9ec-b856986b1422

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasureOrbitRepresentation
import Theorems.Thm_GlobalTheory_HypOrbitUnique_opVec_wI
import Theorems.Thm_PI_RhsWLim_W_ofW_toW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HypOrbitUnique
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU PI.RhsWLim.W.MB
variable {k r : ℕ}
namespace GlobalTheory.HypOrbitUnique
theorem _root_.solution (p : (Fin k → ℂ) × ℂ) : opCo k r (opVec k r p) = p := by
  refine Eq.trans ?_ (ofW_toW p)
  unfold opCo ofW
  simp only [opVec_wI]
end GlobalTheory.HypOrbitUnique
