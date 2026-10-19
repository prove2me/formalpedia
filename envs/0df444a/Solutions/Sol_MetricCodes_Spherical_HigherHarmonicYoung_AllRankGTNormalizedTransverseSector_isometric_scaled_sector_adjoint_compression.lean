-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector.isometric_scaled_sector_adjoint_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/013dd33d-dc29-45d4-905b-313b45d71767

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
set_option maxHeartbeats 3000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
theorem _root_.solution
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    [FiniteDimensional ℝ Z]
    (I : X →ₗᵢ[ℝ] Y) (C : Z →ₗ[ℝ] X)
    (B : Z →ₗᵢ[ℝ] Y) (T : Module.End ℝ Y)
    (phase node : ℝ)
    (hphase : B.toLinearMap = phase • I.toLinearMap.comp C)
    (hnode : ∀ p : Z,
      I.toLinearMap.adjoint (T (I (C p))) = node • C p) :
    B.toLinearMap.adjoint.comp (T.comp B.toLinearMap) =
      node • LinearMap.id := by
  apply LinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro q
  simp only [LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rw [LinearMap.adjoint_inner_right, real_inner_smul_right]
  have hinner := B.inner_map_map q p
  change ⟪B.toLinearMap q, B.toLinearMap p⟫_ℝ = ⟪q, p⟫_ℝ at hinner
  rw [hphase] at hinner ⊢
  change
    ⟪phase • I (C q), T (phase • I (C p))⟫_ℝ =
      node * ⟪q, p⟫_ℝ
  change
    ⟪phase • I (C q), phase • I (C p)⟫_ℝ =
      ⟪q, p⟫_ℝ at hinner
  rw [real_inner_smul_left, real_inner_smul_right,
    I.inner_map_map] at hinner
  have hpair :
      ⟪I (C q), T (I (C p))⟫_ℝ =
        node * ⟪C q, C p⟫_ℝ := by
    change
      ⟪I.toLinearMap (C q), T (I (C p))⟫_ℝ =
        node * ⟪C q, C p⟫_ℝ
    rw [← LinearMap.adjoint_inner_right I.toLinearMap (C q)
      (T (I (C p))), hnode p, real_inner_smul_right]
  rw [map_smul, real_inner_smul_left, real_inner_smul_right,
    hpair, ← hinner]
  ring
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
