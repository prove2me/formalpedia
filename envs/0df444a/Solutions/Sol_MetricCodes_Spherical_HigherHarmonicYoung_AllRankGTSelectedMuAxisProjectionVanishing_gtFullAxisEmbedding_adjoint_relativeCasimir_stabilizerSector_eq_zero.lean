-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing.gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/cd4e22e8-8459-4051-b466-8c89e9cd7294

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_BranchingDimension_fullBranchSignature_antitone
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRankBranching_fullBranchOfInterlaces_signature_eq_appendZeroWeight
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_youngRotationIntertwiner_eq_zero_of_signature_ne
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankZeroRowRotationEquivariance_appendZeroRowIsometryEquiv_symm_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedMuAxisProjectionVanishing_gtRelativeCasimir_tensorAmbientRotation_commute
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedMuAxisProjectionVanishing_gtFullAxisEmbedding_rotation_intertwine
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
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hmu : Interlaces lam mu)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight lam)
    (hne : fullBranchSignature nu ≠ appendZeroWeight mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullAxisEmbedding (n := n) lam (by omega) nu).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) = 0 := by
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let F := (gtFullAxisEmbedding (n := n) lam (by omega) nu).toLinearMap
  let Bpad := B.comp Z.symm.toLinearMap
  let C := (gtRelativeCasimir (n := n + 1) lam).comp Bpad
  have hdom : Antitone (appendZeroWeight lam) :=
    (fullBranchSignature_interlaces_appendZeroWeight lam
      (fullBranchOfInterlaces mu hmu)).antitone_ambient
  have hdommu : Antitone (appendZeroWeight mu) := by
    rw [← fullBranchOfInterlaces_signature_eq_appendZeroWeight mu hmu]
    exact fullBranchSignature_antitone (fullBranchOfInterlaces mu hmu)
  have hBpad (a b : Fin n) :
      Bpad.comp (youngAmbientRotation (appendZeroWeight mu) a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp Bpad := by
    apply LinearMap.ext
    intro q
    have hZ := LinearMap.congr_fun
      (appendZeroRowIsometryEquiv_symm_rotation_intertwine mu a b) q
    have hactual := LinearMap.congr_fun (hB a b) (Z.symm q)
    change B (Z.symm (youngAmbientRotation
      (appendZeroWeight mu) a b q)) =
        tensorAmbientRotation lam a.castSucc b.castSucc
          (B (Z.symm q))
    exact (congrArg B hZ).trans hactual
  have hC (a b : Fin n) :
      C.comp (youngAmbientRotation (appendZeroWeight mu) a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp C := by
    calc
      C.comp (youngAmbientRotation (appendZeroWeight mu) a b) =
        (gtRelativeCasimir (n := n + 1) lam).comp
          (Bpad.comp (youngAmbientRotation (appendZeroWeight mu) a b)) := by
            ext q
            rfl
      _ = (gtRelativeCasimir (n := n + 1) lam).comp
          ((tensorAmbientRotation lam a.castSucc b.castSucc).comp Bpad) := by
            rw [hBpad a b]
      _ = ((gtRelativeCasimir (n := n + 1) lam).comp
          (tensorAmbientRotation lam a.castSucc b.castSucc)).comp Bpad := by
            ext q
            rfl
      _ = ((tensorAmbientRotation lam a.castSucc b.castSucc).comp
          (gtRelativeCasimir (n := n + 1) lam)).comp Bpad := by
            rw [gtRelativeCasimir_tensorAmbientRotation_commute
              (by omega) lam hdom a.castSucc b.castSucc]
      _ = (tensorAmbientRotation lam a.castSucc b.castSucc).comp C := by
            ext q
            rfl
  have hzero : F.adjoint.comp C = 0 := by
    apply youngRotationIntertwiner_eq_zero_of_signature_ne
      (by omega : 2 * ((r + 1) + 1) + 2 ≤ n)
      (appendZeroWeight mu) (fullBranchSignature nu)
      hdommu (Ne.symm hne)
    intro a b
    exact crossGram_intertwines_of_skew F C
      (youngAmbientRotation (fullBranchSignature nu) a b)
      (youngAmbientRotation (appendZeroWeight mu) a b)
      (tensorAmbientRotation lam a.castSucc b.castSucc)
      (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
      (tensorAmbientRotation_adjoint lam a.castSucc b.castSucc)
      (gtFullAxisEmbedding_rotation_intertwine lam (by omega) nu a b)
      (hC a b)
  have hp := LinearMap.congr_fun hzero (Z p)
  change F.adjoint
    (gtRelativeCasimir lam (B (Z.symm (Z p)))) = 0 at hp
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hp
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing
