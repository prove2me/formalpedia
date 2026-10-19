-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors.ambientSumPositiveRoot_highestWeightPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/7d5b0d94-3c25-45c2-abf9-6a6f03c36f51

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_DeterminantVectors_ambientSumPositiveRoot_leadingMinor

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
    (p q : Fin (r + 1)) :
    ambientSumPositiveRoot h p q (highestWeightPolynomial h e) = 0 := by
  classical
  unfold highestWeightPolynomial
  apply derivation_prod_eq_zero
  intro k _
  rw [(ambientSumPositiveRoot h p q).leibniz_pow,
    ambientSumPositiveRoot_leadingMinor h p q k]
  simp
end MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
