-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors.ambientShortPositiveRoot_leadingMinor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/d4a6c9a2-9db2-4bf3-917e-ff58e2916b55

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
    (p k : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientShortPositiveRoot h p t (leadingMinor h k) = 0 := by
  unfold leadingMinor
  apply derivation_det_eq_zero
  intro a b
  exact ambientShortPositiveRoot_isotropicVariable h p
    (minorIndex k a) (minorIndex k b) t ht
end MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
