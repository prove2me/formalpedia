-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance.appendZeroRowIsometryEquiv_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/b7fe8cb9-138b-4cc5-a0a1-0e82a4621c6d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankZeroRowRotationEquivariance_ambientRotation_zeroRowPolynomial

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
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (a b : Fin n) :
    (appendZeroRowIsometryEquiv (n := n) lam).toLinearMap.comp
        (youngAmbientRotation lam a b) =
      (youngAmbientRotation (appendZeroWeight lam) a b).comp
        (appendZeroRowIsometryEquiv (n := n) lam).toLinearMap := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact (ambientRotation_zeroRowPolynomial a b
    (p : PolynomialSpace r n)).symm
end MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
