-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.gtChannelCharacteristic_derivative_eval_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/06dac4be-2888-41d7-a7cf-8dae7086cc1c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCharacteristicResidue_signedAmbientCharacteristic_derivative_eval_pos

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
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    (gtChannelCharacteristicPolynomial n lam).derivative.eval
        (ambientShift n lam row) =
      activeDenominator (ambientShift n lam) row :=
  signedAmbientCharacteristic_derivative_eval_pos
    (ambientShift n lam) row
end MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
