-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalChannelRange.physicalPaddedPieriChannel_relativeCasimir
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/973d9b32-26aa-46c2-9a07-eaa729ee1083

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankZeroRowTensorCasimirConjugacy_zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTInvalidNonterminalProjectorVanishing_paddedOrthogonalTensorPieriChannel_relativeCasimir

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
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalChannelRange
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartHighest
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalEigenchannelEigenspace
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalChannelRange
theorem _root_.solution
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (low : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight low))
    (channel : PaddedPieriChannel (appendZeroWeight low))
    (q : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight low) channel)) :
    gtRelativeCasimir low
        (physicalPaddedPieriChannel hn low hdom channel q) =
      signedNode (HigherChannel.ambientShift n (appendZeroWeight low))
          (paddedPieriSignedChannel (appendZeroWeight low) channel) •
        physicalPaddedPieriChannel hn low hdom channel q := by
  exact zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
    low (paddedOrthogonalTensorPieriChannel
      hn (appendZeroWeight low) hdom channel)
    (zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine low).symm
    (signedNode (HigherChannel.ambientShift n (appendZeroWeight low))
      (paddedPieriSignedChannel (appendZeroWeight low) channel)) q
    (paddedOrthogonalTensorPieriChannel_relativeCasimir
      hn (appendZeroWeight low) hdom channel q)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalChannelRange
