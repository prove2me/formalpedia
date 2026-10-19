-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance.appendZeroRowIsometryEquiv_symm_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/e03e9757-bd10-47ee-befd-051fc52ebc66

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankZeroRowRotationEquivariance_appendZeroRowIsometryEquiv_rotation_intertwine

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
    (appendZeroRowIsometryEquiv (n := n) lam).symm.toLinearMap.comp
        (youngAmbientRotation (appendZeroWeight lam) a b) =
      (youngAmbientRotation lam a b).comp
        (appendZeroRowIsometryEquiv (n := n) lam).symm.toLinearMap := by
  apply LinearMap.ext
  intro p
  have h := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_rotation_intertwine lam a b)
    ((appendZeroRowIsometryEquiv (n := n) lam).symm p)
  have hp := congrArg
    (appendZeroRowIsometryEquiv (n := n) lam).symm h
  simpa using hp.symm
end MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
