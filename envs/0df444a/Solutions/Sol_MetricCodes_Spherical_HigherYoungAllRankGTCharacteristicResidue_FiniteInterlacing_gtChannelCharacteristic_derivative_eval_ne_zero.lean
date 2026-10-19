-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.FiniteInterlacing.gtChannelCharacteristic_derivative_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/aa8d4a20-36c4-4e2b-bb2c-4a73fec26e14

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCharacteristicResidue_gtChannelCharacteristic_derivative_eval_pos
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCharacteristicResidue_gtChannelCharacteristic_derivative_eval_neg

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
namespace FiniteInterlacing
theorem _root_.solution
    {r n : ℕ} {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu)
    (row : Fin (r + 1)) (sign : Bool) :
    (gtChannelCharacteristicPolynomial n lam).derivative.eval
      (signedNode (ambientShift n lam) (row, sign)) ≠ 0 := by
  cases sign
  · simp only [signedNode, Bool.false_eq_true, ↓reduceIte,
      gtChannelCharacteristic_derivative_eval_neg, neg_ne_zero]
    exact h.activeDenominator_ne_zero row
  · simp only [signedNode, ↓reduceIte,
      gtChannelCharacteristic_derivative_eval_pos]
    exact h.activeDenominator_ne_zero row
end FiniteInterlacing
end MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
