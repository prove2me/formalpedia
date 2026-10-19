-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing.signedCharacteristicProjector_canonicalAxis_eq_zero_of_matching_noninterlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/4aae9cb9-869c-4854-866a-175dffb13d48

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_paddedPieriSource_retained_eq_appendZero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_retainedPaddedPieriSignedNode_injective
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_transportedPaddedPieriChannel_eigen_of_retained
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAbsentSignedProjectorOnRetainedSpan_gtCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransportedPieriOrthogonality_physicalPaddedPieriChannel_inner_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalInvalidRowProjectorVanishing_interlaces_of_appendZeroWeight
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalInvalidRowProjectorVanishing_physicalPaddedPieriChannel_adjoint_canonicalAxis_eq_zero_of_not_interlaces
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalInvalidRowProjectorVanishing_canonicalAxis_mem_retainedPhysicalPieriSpan

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
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (selected : Fin (r + 2) × Bool)
    (hbad : ∀ i : {j : PaddedPieriChannel (appendZeroWeight lam) //
        retainedPaddedPieriChannel lam j},
      retainedPaddedPieriSignedNode lam i = selected →
        ¬ Interlaces (retainedPaddedPieriPhysicalSource lam i) mu)
    (p : HarmonicYoungSpace (n := n) mu) :
    signedCharacteristicProjector (HigherChannel.ambientShift (n + 1) lam)
      (gtRelativeCasimir lam) selected
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  classical
  let hfamily : 2 * (r + 2) + 4 ≤ n + 1 := by omega
  let hpadded := appendZeroWeight_antitone lam hfinite.antitone_ambient
  let A := physicalPaddedPieriChannel hfamily lam hpadded
  change gtCharacteristicProjector lam selected
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0
  apply gtCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
    lam mu hfinite (retainedPaddedPieriSignedNode lam)
    (retainedPaddedPieriSignedNode_injective lam)
    (fun i => A i.val)
  · intro i j hij u v
    exact physicalPaddedPieriChannel_inner_eq_zero hfamily lam hpadded
      i.val j.val (fun heq => hij (Subtype.ext heq)) u v
  · intro i q
    exact transportedPaddedPieriChannel_eigen_of_retained
      hfamily lam hpadded i q
  · exact canonicalAxis_mem_retainedPhysicalPieriSpan
      lam mu h hgram hfinite.antitone_ambient hn p
  · intro i hi
    apply physicalPaddedPieriChannel_adjoint_canonicalAxis_eq_zero_of_not_interlaces
      lam mu h hgram hfinite.antitone_ambient hn i.val
    intro hsource
    apply hbad i hi
    apply interlaces_of_appendZeroWeight
      (retainedPaddedPieriPhysicalSource lam i) mu
    rw [← paddedPieriSource_retained_eq_appendZero lam i]
    exact hsource
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing
