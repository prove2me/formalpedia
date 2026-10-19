-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.characteristicResidue_scaled_unique_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/09470b2c-5372-4687-9c57-2446f9bbab6a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCharacteristicResidue_characteristicResidue_unique_of_resolvent

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
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℝ) (hinjective : Function.Injective nodes)
    (numerator : Polynomial ℝ) (weight : ι → ℝ) (scale : ℝ)
    (hresolvent : ∀ z : ℝ, (∀ i : ι, z ≠ nodes i) →
      scale * numerator.eval z /
          (Lagrange.nodal (Finset.univ : Finset ι) nodes).eval z =
        ∑ i : ι, weight i / (z - nodes i))
    (i : ι) :
    weight i = scale * numerator.eval (nodes i) /
      (Lagrange.nodal (Finset.univ : Finset ι) nodes).derivative.eval
        (nodes i) := by
  have h := characteristicResidue_unique_of_resolvent
    nodes hinjective (Polynomial.C scale * numerator) weight (by
      intro z hz
      simpa [Polynomial.eval_mul] using hresolvent z hz) i
  simpa [Polynomial.eval_mul] using h
end MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
