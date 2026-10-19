-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.signedAmbientCharacteristic_derivative_eval_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/b6040bc6-feae-4ee9-a9d1-4e9a3fd2cc6e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_signedNode_denominator_pos_eq_active

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
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
theorem _root_.solution {r : ℕ}
    (L : Fin (r + 1) → ℝ) (row : Fin (r + 1)) :
    (signedAmbientCharacteristic L).derivative.eval (L row) =
      activeDenominator L row := by
  classical
  change Polynomial.eval (L row)
    (Polynomial.derivative
      (Lagrange.nodal
        (Finset.univ : Finset (Fin (r + 1) × Bool))
        (signedNode L))) = _
  have hnode : signedNode L (row, true) = L row := by
    simp [signedNode]
  rw [← hnode,
    Lagrange.eval_nodal_derivative_eval_node_eq
      (Finset.mem_univ (row, true)),
    Lagrange.eval_nodal]
  simpa [hnode] using signedNode_denominator_pos_eq_active L row
end MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
