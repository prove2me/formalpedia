-- Prove2me | solution 1 for GlobalTheory.HypOrbitUnique.opVec_wI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:41.854808+00:00
-- url     : https://prove2.me/submissions/c59d2595-733c-448d-958d-4a4b1a43696e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasureOrbitRepresentation

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
theorem _root_.solution (p : (Fin k → ℂ) × ℂ) (m : Fin (k + 1)) : opVec k r p (wI k r m) = toW k p m := by
  have := m.isLt
  unfold opVec toW wI
  by_cases h : m.val < k
  · rw [dif_pos (by simp only; omega), dif_pos h]
    exact congrArg p.1 (Fin.ext (by simp))
  · rw [dif_neg (by simp only; omega), dif_neg h, if_pos (by simp only; omega)]
end GlobalTheory.HypOrbitUnique
