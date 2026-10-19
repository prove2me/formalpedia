-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport.paddedPieriSource_retained_eq_appendZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/ef9eb7f1-b0d1-408b-bffe-beab9e8f533a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_raiseWeight_appendZeroWeight_castSucc
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_loweredInternalYoungWeight_appendZeroWeight_castSucc

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
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (i : {j : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam j}) :
    paddedPieriSource (appendZeroWeight lam) i.val =
      appendZeroWeight (retainedPaddedPieriPhysicalSource lam i) := by
  rcases i with ⟨(row | row), hrow⟩
  · change raiseWeight (appendZeroWeight lam) row.val =
      appendZeroWeight (raiseWeight lam (row.val.castPred hrow))
    calc
      raiseWeight (appendZeroWeight lam) row.val =
          raiseWeight (appendZeroWeight lam)
            (row.val.castPred hrow).castSucc := by
              rw [Fin.castSucc_castPred]
      _ = _ := raiseWeight_appendZeroWeight_castSucc lam _
  · change loweredInternalYoungWeight (appendZeroWeight lam) row.val =
      appendZeroWeight (loweredInternalYoungWeight lam
        (row.val.castPred (paddedPieriLowerRow_ne_last lam row)))
    calc
      loweredInternalYoungWeight (appendZeroWeight lam) row.val =
          loweredInternalYoungWeight (appendZeroWeight lam)
            (row.val.castPred
              (paddedPieriLowerRow_ne_last lam row)).castSucc := by
                rw [Fin.castSucc_castPred]
      _ = _ := loweredInternalYoungWeight_appendZeroWeight_castSucc lam _
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
