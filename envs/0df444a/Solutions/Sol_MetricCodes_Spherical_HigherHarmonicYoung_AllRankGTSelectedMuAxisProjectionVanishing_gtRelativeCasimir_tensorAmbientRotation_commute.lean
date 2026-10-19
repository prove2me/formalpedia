-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing.gtRelativeCasimir_tensorAmbientRotation_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/458e9ab6-7c38-499e-a3fc-f58175a8be0a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalBranchCompleteness_orthogonalBranch_iSup_range_eq_top
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransportedPieriOrthogonality_physicalPaddedPieriChannel_inner_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransportedPieriOrthogonality_physicalPaddedPieriChannel_finrank
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedPhysicalChannelRange_physicalPaddedPieriChannel_relativeCasimir
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalPaddedPieriFullEigen_physicalPaddedPieriChannel_relativeCasimir
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedMuAxisProjectionVanishing_physicalPaddedPieriChannel_rotation_intertwine
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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriFullEigen
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing
theorem _root_.solution
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (a b : Fin n) :
    (gtRelativeCasimir (n := n) lam).comp
        (tensorAmbientRotation lam a b) =
      (tensorAmbientRotation lam a b).comp
        (gtRelativeCasimir (n := n) lam) := by
  classical
  let A := physicalPaddedPieriChannel hn lam hdom
  have hcomplete :
      (⨆ i : PaddedPieriChannel (appendZeroWeight lam),
        LinearMap.range (A i).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) lam)) :=
    orthogonalBranch_iSup_range_eq_top A
      (physicalPaddedPieriChannel_inner_eq_zero hn lam hdom)
      (physicalPaddedPieriChannel_finrank hn lam hdom)
  apply LinearMap.ext
  intro x
  have hx : x ∈ ⨆ i : PaddedPieriChannel (appendZeroWeight lam),
      LinearMap.range (A i).toLinearMap := by
    rw [hcomplete]
    trivial
  change
    gtRelativeCasimir lam (tensorAmbientRotation lam a b x) =
      tensorAmbientRotation lam a b (gtRelativeCasimir lam x)
  refine Submodule.iSup_induction
    (motive := fun x =>
      gtRelativeCasimir lam (tensorAmbientRotation lam a b x) =
        tensorAmbientRotation lam a b (gtRelativeCasimir lam x))
    _ hx ?_ ?_ ?_
  · intro i x hxi
    obtain ⟨p, rfl⟩ := hxi
    let d := signedNode
      (HigherChannel.ambientShift n (appendZeroWeight lam))
      (paddedPieriSignedChannel (appendZeroWeight lam) i)
    have hrot := LinearMap.congr_fun
      (physicalPaddedPieriChannel_rotation_intertwine hn lam hdom i a b) p
    change
      A i (youngAmbientRotation
        (paddedPieriSource (appendZeroWeight lam) i) a b p) =
        tensorAmbientRotation lam a b (A i p) at hrot
    have heigen (q : HarmonicYoungSpace (n := n)
        (paddedPieriSource (appendZeroWeight lam) i)) :
        gtRelativeCasimir lam (A i q) = d • A i q := by
      simpa only [A, d] using
        physicalPaddedPieriChannel_relativeCasimir hn lam hdom i q
    calc
      gtRelativeCasimir lam
          (tensorAmbientRotation lam a b (A i p)) =
        gtRelativeCasimir lam
          (A i (youngAmbientRotation
            (paddedPieriSource (appendZeroWeight lam) i) a b p)) :=
          congrArg (gtRelativeCasimir lam) hrot.symm
      _ = d • A i (youngAmbientRotation
          (paddedPieriSource (appendZeroWeight lam) i) a b p) :=
          heigen _
      _ = d • tensorAmbientRotation lam a b (A i p) :=
          congrArg (d • ·) hrot
      _ = tensorAmbientRotation lam a b (d • A i p) :=
          (map_smul (tensorAmbientRotation lam a b) d (A i p)).symm
      _ = tensorAmbientRotation lam a b
            (gtRelativeCasimir lam (A i p)) :=
          congrArg (tensorAmbientRotation lam a b) (heigen p).symm
  · simp
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing
