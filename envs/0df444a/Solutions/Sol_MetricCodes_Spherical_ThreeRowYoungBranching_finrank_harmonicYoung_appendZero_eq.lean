-- Prove2me | solution 1 for MetricCodes.Spherical.ThreeRowYoungBranching.finrank_harmonicYoung_appendZero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/257d941e-77d7-4a82-8e63-08e126bdaa9e

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
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.ThreeRowYoungBranching
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
namespace MetricCodes.Spherical.ThreeRowYoungBranching
theorem _root_.solution {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    Module.finrank ℝ
        (HarmonicYoungSpace (n := n) (appendZeroWeight mu)) =
      Module.finrank ℝ (HarmonicYoungSpace (n := n) mu) :=
  (appendZeroRowIsometryEquiv (n := n) mu).toLinearEquiv.finrank_eq.symm
end MetricCodes.Spherical.ThreeRowYoungBranching
