-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors.ambientPositiveRoot_dominantHighestWeightWitness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/1837ba0b-e154-49d9-b5c2-fec959604fd4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_DeterminantVectors_ambientPositiveRoot_highestWeightPolynomial

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
    (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (p q : Fin (r + 1)) (hpq : p < q) :
    ambientPositiveRoot h p q
        (dominantHighestWeightWitness h lam hdom).polynomial = 0 := by
  exact ambientPositiveRoot_highestWeightPolynomial h
    (signatureExponent lam) p q hpq
end MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
