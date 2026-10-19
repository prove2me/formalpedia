-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy.zeroRowTensorIsometryEquiv_symm_tensorCasimir_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/3b837c33-e2b5-4acc-b36f-9acae3dc6c16

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankZeroRowTensorCasimirConjugacy_zeroRowTensorIsometryEquiv_symm_rotation_intertwine

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
        (gtTensorCasimir (appendZeroWeight lam)) =
      (gtTensorCasimir lam).comp
        (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  have hrot (a b : Fin n)
      (y : SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (appendZeroWeight lam)) :
      (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap
          (tensorAmbientRotation (appendZeroWeight lam) a b y) =
        tensorAmbientRotation lam a b
          ((zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap y) :=
    LinearMap.congr_fun
      (zeroRowTensorIsometryEquiv_symm_rotation_intertwine lam a b) y
  simp only [LinearMap.comp_apply, gtTensorCasimir, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.neg_apply, map_smul, map_sum, map_neg]
  simp_rw [hrot]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
