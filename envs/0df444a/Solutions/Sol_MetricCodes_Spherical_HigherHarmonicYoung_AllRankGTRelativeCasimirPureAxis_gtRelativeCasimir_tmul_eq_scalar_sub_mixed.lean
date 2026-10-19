-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis.gtRelativeCasimir_tmul_eq_scalar_sub_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/73566e23-4e60-4f3f-9c71-efa81c317b2a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirPureAxis_gtEuclideanCasimir_eq_smul_id
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirPureAxis_gtTensorCasimir_tmul_eq_vector_add_young_sub_mixed

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
open scoped BigOperators TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    gtRelativeCasimir lam (v ⊗ₜ[ℝ] p) =
      (((n : ℝ) - 2) / 2) • (v ⊗ₜ[ℝ] p) -
        (2 : ℝ)⁻¹ • gtMixedRotationOperator lam (v ⊗ₜ[ℝ] p) := by
  simp only [gtRelativeCasimir, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  rw [gtTensorCasimir_tmul_eq_vector_add_young_sub_mixed,
    gtEuclideanCasimir_eq_smul_id,
    youngAmbientCasimir_allRank_eq_smul_id]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  module
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
