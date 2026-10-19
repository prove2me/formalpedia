-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing.paddedOrthogonalTensorPieriChannel_relativeCasimir
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/352090cf-62a0-49d2-bc46-8fa9b1b46f52

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_raise_channel
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_lower_channel
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriActualChannels_paddedOrthogonalTensorPieriChannel_rotation_intertwine

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
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNoninterlacingTensorChannelAxisOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing
theorem _root_.solution
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (i : PaddedPieriChannel target)
    (p : HarmonicYoungSpace (n := n) (paddedPieriSource target i)) :
    gtRelativeCasimir target
        (paddedOrthogonalTensorPieriChannel hn target hdom i p) =
      signedNode (HigherChannel.ambientShift n target)
        (paddedPieriSignedChannel target i) •
        paddedOrthogonalTensorPieriChannel hn target hdom i p := by
  cases i with
  | inl row =>
      exact gtRelativeCasimir_raise_channel target row.val
        (paddedOrthogonalTensorPieriChannel hn target hdom
          (Sum.inl row)).toLinearMap
        (paddedOrthogonalTensorPieriChannel_rotation_intertwine
          hn target hdom (Sum.inl row)) p
  | inr row =>
      have hsource : target =
          raiseWeight (paddedPieriSource target (Sum.inr row)) row.val :=
        (raiseWeight_loweredInternalYoungWeight
          target row.val row.property.1).symm
      exact gtRelativeCasimir_lower_channel target
        (paddedPieriSource target (Sum.inr row)) row.val hsource
        (paddedOrthogonalTensorPieriChannel hn target hdom
          (Sum.inr row)).toLinearMap
        (paddedOrthogonalTensorPieriChannel_rotation_intertwine
          hn target hdom (Sum.inr row)) p
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing
