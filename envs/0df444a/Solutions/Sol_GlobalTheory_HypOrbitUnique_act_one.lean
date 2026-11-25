-- Prove2me | solution 1 for GlobalTheory.HypOrbitUnique.act_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:27:32.12732+00:00
-- url     : https://prove2.me/submissions/20a10c76-f272-4994-a0f3-5624d4131539

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasureOrbitRepresentation
import Theorems.Thm_GlobalTheory_HypOrbitUnique_opCo_opVec

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
theorem _root_.solution (p : (Fin k → ℂ) × ℂ) : act (1 : Gp k r) p = p := by
  have e : (Matrix.of (inc (1 : Gp k r)) : Mat k r) = 1 := rfl
  unfold act opAct
  rw [e, Matrix.one_mulVec, opCo_opVec]
end GlobalTheory.HypOrbitUnique
