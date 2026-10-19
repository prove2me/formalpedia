-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange.linearIsometry_projection_mem_range_of_adjoint_coordinate_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/a5b98cf3-9595-45c3-b9e6-32b08ef75357

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.gtTransverseWallTensorEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_toLinearMap
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_apply
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition.gtFullTransverseInternalEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition.gtFullAxisEmbedding_apply

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
set_option autoImplicit false
open scoped InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartHighest
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange
theorem _root_.solution
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    [FiniteDimensional ℝ Z]
    (F : X →ₗᵢ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (hBF : LinearMap.range B ≤ LinearMap.range F.toLinearMap)
    (v : Y)
    (hcoordinate : F.toLinearMap.adjoint v ∈
      LinearMap.range (F.toLinearMap.adjoint.comp B)) :
    F (F.toLinearMap.adjoint v) ∈ LinearMap.range B := by
  obtain ⟨p, hp⟩ := hcoordinate
  obtain ⟨x, hx⟩ := hBF ⟨p, rfl⟩
  have hself := LinearMap.congr_fun F.adjoint_comp_self' x
  have hself' : F.toLinearMap.adjoint (F.toLinearMap x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hself
  have hcoord : F.toLinearMap.adjoint (B p) =
      F.toLinearMap.adjoint v := by
    simpa only [LinearMap.comp_apply] using hp
  change F.toLinearMap (F.toLinearMap.adjoint v) ∈ LinearMap.range B
  refine ⟨p, ?_⟩
  calc
    B p = F.toLinearMap x := hx.symm
    _ = F.toLinearMap
      (F.toLinearMap.adjoint (F.toLinearMap x)) :=
        congrArg F.toLinearMap hself'.symm
    _ = F.toLinearMap (F.toLinearMap.adjoint (B p)) :=
      congrArg (fun y : Y => F.toLinearMap (F.toLinearMap.adjoint y)) hx
    _ = F.toLinearMap (F.toLinearMap.adjoint v) :=
      congrArg F.toLinearMap hcoord
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange
