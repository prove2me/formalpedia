-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAmbientCharacteristicAtTransverseNode.signedAmbientCharacteristic_eval_ne_zero_of_forall_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/38bcf56c-67d3-47c4-9514-c5e3940c8655

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAmbientCharacteristicAtTransverseNode
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAmbientCharacteristicAtTransverseNode
theorem _root_.solution
    {r : ℕ} (L : Fin (r + 1) → ℝ) (d : ℝ)
    (hnode : ∀ i : Fin (r + 1) × Bool, d ≠ signedNode L i) :
    (signedAmbientCharacteristic L).eval d ≠ 0 := by
  unfold signedAmbientCharacteristic
  apply Lagrange.eval_nodal_not_at_node
  intro i _
  exact hnode i
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAmbientCharacteristicAtTransverseNode
