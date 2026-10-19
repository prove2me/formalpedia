-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy.zeroRowTensorIsometryEquiv_symm_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/916b477d-7a8c-435f-b68c-9b593a14e7d9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankZeroRowRotationEquivariance_appendZeroRowIsometryEquiv_symm_rotation_intertwine

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
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (a b : Fin n) :
    (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap.comp
        (tensorAmbientRotation (appendZeroWeight lam) a b) =
      (tensorAmbientRotation lam a b).comp
        (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap := by
  apply TensorProduct.ext'
  intro v p
  change (zeroRowTensorIsometryEquiv (n := n) lam).symm
      (tensorAmbientRotation (appendZeroWeight lam) a b (v ⊗ₜ[ℝ] p)) =
    tensorAmbientRotation lam a b
      ((zeroRowTensorIsometryEquiv (n := n) lam).symm (v ⊗ₜ[ℝ] p))
  simp only [tensorAmbientRotation_tmul, map_add,
    zeroRowTensorIsometryEquiv_symm_tmul]
  congr 1
  exact congrArg (fun q => v ⊗ₜ[ℝ] q)
    (LinearMap.congr_fun
      (appendZeroRowIsometryEquiv_symm_rotation_intertwine lam a b) p)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
