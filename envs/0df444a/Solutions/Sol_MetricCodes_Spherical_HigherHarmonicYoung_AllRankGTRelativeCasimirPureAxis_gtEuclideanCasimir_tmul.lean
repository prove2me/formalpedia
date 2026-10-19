-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis.gtEuclideanCasimir_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/0ce0c217-2760-4891-883f-e5458b0a42c5

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
    (gtEuclideanCasimir n v) ⊗ₜ[ℝ] p =
      (2 : ℝ)⁻¹ • ∑ a : Fin n, ∑ b : Fin n,
        -((euclideanAmbientRotation a b
          (euclideanAmbientRotation a b v)) ⊗ₜ[ℝ] p) := by
  simp only [gtEuclideanCasimir, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.neg_apply, LinearMap.comp_apply]
  rw [← TensorProduct.smul_tmul']
  congr 1
  change
    ((TensorProduct.mk ℝ (SpherePacking.Euclidean n)
      (HarmonicYoungSpace (n := n) lam)).flip p)
        (∑ a : Fin n, ∑ b : Fin n,
          -(euclideanAmbientRotation a b
            (euclideanAmbientRotation a b v))) = _
  rw [map_sum]
  simp_rw [map_sum, map_neg]
  rfl
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
