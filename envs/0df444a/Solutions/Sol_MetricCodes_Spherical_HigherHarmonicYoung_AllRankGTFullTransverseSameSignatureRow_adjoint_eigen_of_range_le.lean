-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow.adjoint_eigen_of_range_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/f5202ff2-8143-43ae-a853-f227bec12589

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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
theorem _root_.solution
    {X Y H : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (I : X →ₗ[ℝ] H) (J : Y →ₗ[ℝ] H)
    (hrange : LinearMap.range J ≤ LinearMap.range I)
    (T : Module.End ℝ H) (x : H) (d : ℝ)
    (hI : I.adjoint (T x) = d • I.adjoint x) :
    J.adjoint (T x) = d • J.adjoint x := by
  apply ext_inner_left ℝ
  intro q
  obtain ⟨z, hz⟩ := hrange (show J q ∈ LinearMap.range J from ⟨q, rfl⟩)
  calc
    ⟪q, J.adjoint (T x)⟫_ℝ = ⟪J q, T x⟫_ℝ :=
      LinearMap.adjoint_inner_right J q (T x)
    _ = ⟪I z, T x⟫_ℝ := by rw [hz]
    _ = ⟪z, I.adjoint (T x)⟫_ℝ :=
      (LinearMap.adjoint_inner_right I z (T x)).symm
    _ = ⟪z, d • I.adjoint x⟫_ℝ := by rw [hI]
    _ = d * ⟪z, I.adjoint x⟫_ℝ := real_inner_smul_right z (I.adjoint x) d
    _ = d * ⟪I z, x⟫_ℝ := by rw [LinearMap.adjoint_inner_right]
    _ = d * ⟪J q, x⟫_ℝ := by rw [hz]
    _ = ⟪q, d • J.adjoint x⟫_ℝ := by
      rw [real_inner_smul_right, LinearMap.adjoint_inner_right]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
