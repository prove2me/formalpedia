-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing.physicalPaddedPieriChannel_adjoint_canonicalAxis_eq_zero_of_not_interlaces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/0b534607-fed4-442e-8bdc-068ad5aca6a4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriActualChannels_paddedOrthogonalTensorPieriChannel_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTIllegalStabilizerIntertwiner_illegalYoungStabilizerIntertwiner_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTNoninterlacingTensorChannelAxisOrthogonality_paddedPieriSource_antitone
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAppendedPieriPhysicalAxisOrthogonality_originalPaddedSelectedAxisTensor_rotation_intertwine

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
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedPieriPhysicalAxisOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTIllegalStabilizerIntertwiner
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNoninterlacingTensorChannelAxisOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdom : Antitone lam)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (i : PaddedPieriChannel (appendZeroWeight lam))
    (hbad : ¬ Interlaces (paddedPieriSource (appendZeroWeight lam) i)
      (appendZeroWeight mu))
    (p : HarmonicYoungSpace (n := n) mu) :
    (physicalPaddedPieriChannel (n := n + 1) (by omega) lam
      (appendZeroWeight_antitone lam hdom) i).toLinearMap.adjoint
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  let hpadded := appendZeroWeight_antitone lam hdom
  let C := (paddedOrthogonalTensorPieriChannel
    (by omega : 2 * (r + 2) + 4 ≤ n + 1)
    (appendZeroWeight lam) hpadded i).toLinearMap
  let A := originalPaddedSelectedAxisTensor lam mu h hgram
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let W := appendZeroRowIsometryEquiv (n := n) (appendZeroWeight mu)
  let T := zeroRowTensorIsometryEquiv (n := n + 1) lam
  have hcross : C.adjoint.comp A = 0 := by
    apply illegalYoungStabilizerIntertwiner_eq_zero
      (paddedPieriSource (appendZeroWeight lam) i)
      (appendZeroWeight mu) (by omega)
      (paddedPieriSource_antitone (appendZeroWeight lam) i)
      (appendZeroWeight_antitone mu
        (interlaces_antitone_stabilizer h)) hbad
    intro a b
    apply crossGram_intertwines_of_skew C A
      (youngAmbientRotation
        (paddedPieriSource (appendZeroWeight lam) i)
          a.castSucc b.castSucc)
      (youngAmbientRotation (appendZeroWeight (appendZeroWeight mu)) a b)
      (tensorAmbientRotation (appendZeroWeight lam)
        a.castSucc b.castSucc)
      (youngAmbientRotation_adjoint
        (paddedPieriSource (appendZeroWeight lam) i)
          a.castSucc b.castSucc)
      (tensorAmbientRotation_adjoint (appendZeroWeight lam)
        a.castSucc b.castSucc)
    · exact paddedOrthogonalTensorPieriChannel_rotation_intertwine
        (by omega) (appendZeroWeight lam) hpadded i
          a.castSucc b.castSucc
    · exact originalPaddedSelectedAxisTensor_rotation_intertwine
        lam mu h hgram a b
  have hz := LinearMap.congr_fun hcross (W (Z p))
  have hC : C.adjoint (T
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)) = 0 := by
    change C.adjoint
      (T (canonicalGelfandTsetlinAxisTensor lam mu h hgram
        (Z.symm (W.symm (W (Z p)))))) = 0 at hz
    simpa using hz
  apply ext_inner_left ℝ
  intro q
  rw [inner_zero_right, LinearMap.adjoint_inner_right]
  change ⟪T.symm (C q),
    canonicalGelfandTsetlinAxisTensor lam mu h hgram p⟫_ℝ = 0
  calc
    ⟪T.symm (C q),
      canonicalGelfandTsetlinAxisTensor lam mu h hgram p⟫_ℝ =
        ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
          T.symm (C q)⟫_ℝ :=
            real_inner_comm
              (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)
              (T.symm (C q))
    _ = ⟪T (canonicalGelfandTsetlinAxisTensor lam mu h hgram p), C q⟫_ℝ := by
          rw [← T.inner_map_map,
            LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪C.adjoint
        (T (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)), q⟫_ℝ :=
          (LinearMap.adjoint_inner_left C q _).symm
    _ = 0 := by
      rw [hC, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing
