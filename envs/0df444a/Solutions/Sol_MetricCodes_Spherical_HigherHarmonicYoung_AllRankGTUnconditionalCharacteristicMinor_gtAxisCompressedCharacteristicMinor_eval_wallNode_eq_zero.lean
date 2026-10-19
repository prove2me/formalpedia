-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor.gtAxisCompressedCharacteristicMinor_eval_wallNode_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/3dee8647-7dff-4e14-8faa-d79b2841b9e3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAbsentWallCharacteristicFactor_gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero_of_last_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_canonicalAxis_inner_normalizedGTTransverseWallSector_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTNormalizedWallCharacteristicAnnihilation_normalizedGTTransverseWallSector_characteristic_aeval_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPresentWallSignedNodeSeparation_presentWall_ne_signedAmbientNode
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalWallAdditiveColumn_gtRelativeCasimir_normalizedWallSector_additiveColumn
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTValidTransverseMinorRoots_gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero

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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentWallCharacteristicFactor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCharacteristicMinorOfValidRoots
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseCharacteristicAnnihilation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedWallCharacteristicAnnihilation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPresentWallSignedNodeSeparation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalWallAdditiveColumn
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCrossBlock
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseRetainedTwoBlockClosure
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseMinorRoots
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (-(wallShift (n + 1) (r + 1))) = 0 := by
  by_cases hlast : lam (Fin.last (r + 1)) = 0
  · exact gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero_of_last_eq_zero
      lam mu h hgram hfinite hlast p q
  · have hpos : 0 < lam (Fin.last (r + 1)) := Nat.pos_of_ne_zero hlast
    let hw : 2 * (r + 1) + 5 ≤ n + 1 := by omega
    let B := normalizedGTTransverseWallSector lam mu h hw hpos
    let K := gtTransverseAxisCrossBlock lam mu h hgram B.toLinearMap
    exact gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
      lam mu h hgram hfinite hn B (-(wallShift (n + 1) (r + 1))) K
      (fun x y => canonicalAxis_inner_normalizedGTTransverseWallSector_eq_zero
        lam mu h hw hpos hgram x y)
      (gtRelativeCasimir_normalizedWallSector_additiveColumn
        lam mu h hgram hn hpos)
      (fun x => normalizedGTTransverseWallSector_characteristic_aeval_eq_zero
        lam mu h hw hn hpos x)
      (presentWall_ne_signedAmbientNode hfinite hpos)
      p q
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor
