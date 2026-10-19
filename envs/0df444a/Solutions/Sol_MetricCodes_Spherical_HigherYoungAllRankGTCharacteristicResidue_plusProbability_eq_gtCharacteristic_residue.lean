-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.plusProbability_eq_gtCharacteristic_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/e69cd7a6-479a-4395-8be7-0d09e60bfc30

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_channelNumeratorPolynomial_eval_pos
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCharacteristicResidue_gtChannelCharacteristic_derivative_eval_pos

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
theorem _root_.solution {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (row : Fin (r + 1)) :
    plusProbability n lam mu row =
      (channelNumeratorPolynomial (wallShift n r)
          (stabilizerShift n mu)).eval (ambientShift n lam row) /
        (gtChannelCharacteristicPolynomial n lam).derivative.eval
          (ambientShift n lam row) := by
  rw [channelNumeratorPolynomial_eval_pos,
    gtChannelCharacteristic_derivative_eval_pos]
  rfl
end MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
