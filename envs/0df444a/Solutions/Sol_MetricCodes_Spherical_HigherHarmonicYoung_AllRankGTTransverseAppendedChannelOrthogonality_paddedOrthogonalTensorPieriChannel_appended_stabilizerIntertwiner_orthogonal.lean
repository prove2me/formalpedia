-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality.paddedOrthogonalTensorPieriChannel_appended_stabilizerIntertwiner_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/3e3de532-3f8d-47d2-8e67-aef2b37af7e7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseAppendedChannelOrthogonality_appendedPaddedPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero

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
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n + 1)
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    ⟪B p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdominant
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0 := by
  let C := (normalizedPaddedPieriLower (n := n + 1)
    (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).toLinearMap
  let A := paddedPhysicalStabilizerTensor lam mu B
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let W := appendZeroRowIsometryEquiv (n := n) (appendZeroWeight mu)
  let T := zeroRowTensorIsometryEquiv (n := n + 1) lam
  have hzero := LinearMap.congr_fun
    (appendedPaddedPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
      lam mu hmu B hB hdominant hsource hn) (W (Z p))
  have hz : C.adjoint (T (B p)) = 0 := by
    change C.adjoint (A (W (Z p))) = 0 at hzero
    change C.adjoint (T (B (Z.symm (W.symm (W (Z p)))))) = 0 at hzero
    rw [W.symm_apply_apply, Z.symm_apply_apply] at hzero
    exact hzero
  change ⟪B p, T.symm (C q)⟫_ℝ = 0
  calc
    ⟪B p, T.symm (C q)⟫_ℝ =
      ⟪T (B p), T (T.symm (C q))⟫_ℝ :=
        (T.inner_map_map (B p) (T.symm (C q))).symm
    _ = ⟪T (B p), C q⟫_ℝ := by
      rw [LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪C.adjoint (T (B p)), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left C q (T (B p))).symm
    _ = 0 := by
      rw [hz, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality
