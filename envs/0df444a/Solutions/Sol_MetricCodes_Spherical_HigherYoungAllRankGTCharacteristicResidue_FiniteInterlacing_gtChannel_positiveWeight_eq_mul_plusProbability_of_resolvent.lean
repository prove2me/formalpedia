-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.FiniteInterlacing.gtChannel_positiveWeight_eq_mul_plusProbability_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/79daa9dd-6b5c-4f2f-9e0a-4b86b2f9c484

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_signedNode_injective
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCharacteristicResidue_plusProbability_eq_gtCharacteristic_residue
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCharacteristicResidue_characteristicResidue_scaled_unique_of_resolvent

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
    (weight : Fin (r + 1) × Bool → ℝ) (scale : ℝ)
    (hresolvent : ∀ z : ℝ,
      (∀ i : Fin (r + 1) × Bool,
        z ≠ signedNode (ambientShift n lam) i) →
      scale * (channelNumeratorPolynomial (wallShift n r)
          (stabilizerShift n mu)).eval z /
          (gtChannelCharacteristicPolynomial n lam).eval z =
        ∑ i : Fin (r + 1) × Bool,
          weight i / (z - signedNode (ambientShift n lam) i))
    (row : Fin (r + 1)) :
    weight (row, true) = scale * plusProbability n lam mu row := by
  rw [plusProbability_eq_gtCharacteristic_residue lam mu row]
  have hresidue := characteristicResidue_scaled_unique_of_resolvent
    (signedNode (ambientShift n lam))
    (signedNode_injective h.ambientShift_pos
      h.ambientShift_strictAnti.injective)
    (channelNumeratorPolynomial (wallShift n r)
      (stabilizerShift n mu)) weight scale hresolvent (row, true)
  simpa [signedNode, gtChannelCharacteristicPolynomial,
    signedAmbientCharacteristic, div_eq_mul_inv, mul_assoc] using hresidue
end FiniteInterlacing
end MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
