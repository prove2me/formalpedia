-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis.gtYoungCasimir_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/de55abbe-7c07-41ab-a1b0-be90eb1062b4

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
    v ⊗ₜ[ℝ] (youngAmbientCasimir lam p) =
      (2 : ℝ)⁻¹ • ∑ a : Fin n, ∑ b : Fin n,
        -(v ⊗ₜ[ℝ]
          (youngAmbientRotation lam a b
            (youngAmbientRotation lam a b p))) := by
  simp only [youngAmbientCasimir, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.neg_apply, LinearMap.comp_apply]
  rw [TensorProduct.tmul_smul]
  congr 1
  change
    ((TensorProduct.mk ℝ (SpherePacking.Euclidean n)
      (HarmonicYoungSpace (n := n) lam)) v)
        (∑ a : Fin n, ∑ b : Fin n,
          -(youngAmbientRotation lam a b
            (youngAmbientRotation lam a b p))) = _
  rw [map_sum]
  simp_rw [map_sum, map_neg]
  rfl
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
