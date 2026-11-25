-- Prove2me | solution 1 for GlobalTheory.HypOrbitUnique.continuous_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:58.2978+00:00
-- url     : https://prove2.me/submissions/61b1cf64-1adb-4fb7-abbc-a4905954686d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasureOrbitRepresentation
import Theorems.Thm_GlobalTheory_HypOrbitUnique_continuous_opVec

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
theorem _root_.solution : Continuous (Function.uncurry (act (k := k) (r := r))) := by
  have hc : Continuous fun q : Gp k r × ((Fin k → ℂ) × ℂ) =>
      (Matrix.of (inc q.1) : Mat k r) *ᵥ opVec k r q.2 :=
    Continuous.matrix_mulVec (inc_cont.comp continuous_fst) (continuous_opVec.comp continuous_snd)
  exact (continuous_pi fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp hc).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp hc)
end GlobalTheory.HypOrbitUnique
