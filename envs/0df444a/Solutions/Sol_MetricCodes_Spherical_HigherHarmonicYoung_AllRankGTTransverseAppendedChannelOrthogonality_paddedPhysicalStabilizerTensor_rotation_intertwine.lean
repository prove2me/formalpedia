-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality.paddedPhysicalStabilizerTensor_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/c1499d79-e428-44b2-b147-2a239e562302

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankZeroRowRotationEquivariance_appendZeroRowIsometryEquiv_symm_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankZeroRowTensorCasimirConjugacy_zeroRowTensorIsometryEquiv_rotation_intertwine

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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedClebschOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedRowExclusion
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (a b : Fin n) :
    (paddedPhysicalStabilizerTensor lam mu B).comp
        (youngAmbientRotation
          (appendZeroWeight (appendZeroWeight mu)) a b) =
      (tensorAmbientRotation (appendZeroWeight lam)
        a.castSucc b.castSucc).comp
          (paddedPhysicalStabilizerTensor lam mu B) := by
  let T := (zeroRowTensorIsometryEquiv (n := n + 1) lam).toLinearMap
  let Z := (appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap
  let W := (appendZeroRowIsometryEquiv
    (n := n) (appendZeroWeight mu)).symm.toLinearMap
  apply LinearMap.ext
  intro p
  change T (B (Z (W (youngAmbientRotation
    (appendZeroWeight (appendZeroWeight mu)) a b p)))) =
    tensorAmbientRotation (appendZeroWeight lam)
      a.castSucc b.castSucc (T (B (Z (W p))))
  have hW := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine
      (appendZeroWeight mu) a b) p
  have hZ := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine
      mu a b) (W p)
  have hsector := LinearMap.congr_fun (hB a b) (Z (W p))
  have hT := LinearMap.congr_fun
    (zeroRowTensorIsometryEquiv_rotation_intertwine
      lam a.castSucc b.castSucc) (B (Z (W p)))
  exact (congrArg (fun q => T (B (Z q))) hW).trans
    ((congrArg (fun q => T (B q)) hZ).trans
      ((congrArg T hsector).trans hT))
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality
