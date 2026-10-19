-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy.zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/77445471-0695-4a59-9b00-262e4f3711ec

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankZeroRowTensorCasimirConjugacy_zeroRowTensorIsometryEquiv_symm_tensorCasimir_intertwine

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
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap.comp
        (gtRelativeCasimir (appendZeroWeight lam)) =
      (gtRelativeCasimir lam).comp
        (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (zeroRowTensorIsometryEquiv_symm_tensorCasimir_intertwine lam) x
  simp only [LinearMap.comp_apply] at h
  simp only [gtRelativeCasimir, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_sub]
  rw [allRankCasimirEigenvalue_appendZeroWeight, h]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
