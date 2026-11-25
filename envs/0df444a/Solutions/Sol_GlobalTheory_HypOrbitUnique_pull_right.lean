-- Prove2me | solution 1 for GlobalTheory.HypOrbitUnique.pull_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:04.124477+00:00
-- url     : https://prove2.me/submissions/0379062b-5d3a-4dcd-a0d7-553b8486cd8d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasureOrbitRepresentation
import Theorems.Thm_PI_RhsWLim_W_HU_inc_memb
import Theorems.Thm_PI_RhsWLim_W_HU_map_pull
import Theorems.Thm_PI_RhsWLim_W_rmulM_cont


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
theorem _root_.solution (ν : Measure (Mt k r)) (hc : ν {x | Matrix.of x ∉ UWb k r} = 0)
    (h : ∀ p ∈ UWb k r, ν.map (rmulM p) = ν) : (pull ν).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  apply inc_memb.map_injective
  have e : (inc : Gp k r → Mt k r) ∘ (fun x => x * g) = rmulM (Matrix.of (inc g)) ∘ inc := rfl
  show ((pull ν).map (fun x => x * g)).map inc = (pull ν).map inc
  rw [Measure.map_map inc_memb.measurable (continuous_mul_const g).measurable, e,
    ← Measure.map_map (rmulM_cont _).measurable inc_memb.measurable, map_pull ν hc, h _ (inc_mem g)]
end GlobalTheory.HypOrbitUnique
