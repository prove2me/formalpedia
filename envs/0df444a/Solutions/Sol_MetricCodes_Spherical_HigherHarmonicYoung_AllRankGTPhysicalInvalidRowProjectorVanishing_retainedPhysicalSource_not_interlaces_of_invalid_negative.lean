-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing.retainedPhysicalSource_not_interlaces_of_invalid_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/90358b28-a056-4b58-911b-d78b00e54a52

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTInvalidRowCharacteristicMinorVanishing_not_interlaces_raiseWeight_iff_upperWall
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTInvalidRowCharacteristicMinorVanishing_not_interlaces_lowerAmbient_of_upperWall

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
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (row : Fin (r + 1))
    (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (i : {j : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam j})
    (hi : retainedPaddedPieriSignedNode lam i = (row.castSucc, false)) :
    ¬ Interlaces (retainedPaddedPieriPhysicalSource lam i) mu := by
  have hwall : lam row.castSucc = mu row :=
    (not_interlaces_raiseWeight_iff_upperWall lam mu h row).mp hbad
  rcases i with ⟨(actual | actual), hretained⟩
  · have hsign := congrArg Prod.snd hi
    simp [retainedPaddedPieriSignedNode] at hsign
  · have hrow :
        actual.val.castPred (paddedPieriLowerRow_ne_last lam actual) =
          row.castSucc := congrArg Prod.fst hi
    change ¬ Interlaces
      (loweredInternalYoungWeight lam
        (actual.val.castPred (paddedPieriLowerRow_ne_last lam actual))) mu
    rw [hrow]
    apply not_interlaces_lowerAmbient_of_upperWall lam mu row hwall
    have hcast : actual.val = row.castSucc.castSucc := by
      calc
        actual.val =
            (actual.val.castPred
              (paddedPieriLowerRow_ne_last lam actual)).castSucc :=
                (Fin.castSucc_castPred _ _).symm
        _ = row.castSucc.castSucc := congrArg Fin.castSucc hrow
    simpa [hcast] using actual.property.1
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing
