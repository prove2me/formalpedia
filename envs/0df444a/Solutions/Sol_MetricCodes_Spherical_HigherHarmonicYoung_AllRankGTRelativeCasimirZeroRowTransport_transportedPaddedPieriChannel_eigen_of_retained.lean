-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport.transportedPaddedPieriChannel_eigen_of_retained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/99ce267c-cd36-40c3-aca3-c0a880e45610

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_raise_channel
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_lower_channel
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriActualChannels_paddedOrthogonalTensorPieriChannel_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankZeroRowTensorCasimirConjugacy_zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_signedNode_appendZeroWeight_retained_raise
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_signedNode_appendZeroWeight_retained_lower
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_zeroRowTransportPaddedPieriChannel_eigen_of_intertwine

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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
theorem _root_.solution
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (i : {j : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam j})
    (p : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight lam) i.val)) :
    gtRelativeCasimir (n := n) lam
        (zeroRowTransportPaddedPieriChannel lam
          (paddedOrthogonalTensorPieriChannel
            hn (appendZeroWeight lam) hdom i.val) p) =
      signedNode (HigherChannel.ambientShift n lam)
          (retainedPaddedPieriSignedNode lam i) •
        zeroRowTransportPaddedPieriChannel lam
          (paddedOrthogonalTensorPieriChannel
            hn (appendZeroWeight lam) hdom i.val) p := by
  rcases i with ⟨(row | row), hrow⟩
  · have hchannel := gtRelativeCasimir_raise_channel
      (appendZeroWeight lam) row.val
      (paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom (Sum.inl row)).toLinearMap
      (paddedOrthogonalTensorPieriChannel_rotation_intertwine hn
        (appendZeroWeight lam) hdom (Sum.inl row)) p
    have htransport := zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
      lam
      (paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom (Sum.inl row))
      (zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine lam).symm
      (signedNode
        (HigherChannel.ambientShift n (appendZeroWeight lam))
        (row.val, true)) p hchannel
    rw [signedNode_appendZeroWeight_retained_raise lam row hrow]
      at htransport
    exact htransport
  · have hsource : appendZeroWeight lam =
        raiseWeight
          (paddedPieriSource (appendZeroWeight lam) (Sum.inr row)) row.val := by
      simpa using
        (raiseWeight_loweredInternalYoungWeight
          (appendZeroWeight lam) row.val row.property.1).symm
    have hchannel := gtRelativeCasimir_lower_channel
      (appendZeroWeight lam)
      (paddedPieriSource (appendZeroWeight lam) (Sum.inr row)) row.val
      hsource
      (paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom (Sum.inr row)).toLinearMap
      (paddedOrthogonalTensorPieriChannel_rotation_intertwine hn
        (appendZeroWeight lam) hdom (Sum.inr row)) p
    have htransport := zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
      lam
      (paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom (Sum.inr row))
      (zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine lam).symm
      (signedNode
        (HigherChannel.ambientShift n (appendZeroWeight lam))
        (row.val, false)) p hchannel
    rw [signedNode_appendZeroWeight_retained_lower lam row] at htransport
    exact htransport
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
