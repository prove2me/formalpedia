-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors.ambientShortPositiveRoot_highestWeightPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/9758aedf-62f0-4bf1-80a7-a95001fb51ba

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_DeterminantVectors_ambientShortPositiveRoot_leadingMinor

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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
namespace MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
theorem _root_.solution {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ)
    (p : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientShortPositiveRoot h p t (highestWeightPolynomial h e) = 0 := by
  classical
  unfold highestWeightPolynomial
  apply derivation_prod_eq_zero
  intro k _
  rw [(ambientShortPositiveRoot h p t).leibniz_pow,
    ambientShortPositiveRoot_leadingMinor h p k t ht]
  simp
end MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
