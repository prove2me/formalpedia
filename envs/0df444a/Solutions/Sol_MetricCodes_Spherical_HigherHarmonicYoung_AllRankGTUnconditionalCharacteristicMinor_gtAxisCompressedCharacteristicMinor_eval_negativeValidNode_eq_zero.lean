-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor.gtAxisCompressedCharacteristicMinor_eval_negativeValidNode_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/4130ef0d-a0b6-454a-9df0-add8e71b4d3b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTNormalizedTransverseSector_normalizedGTTransverseNegativeSector_relativeCasimir_adjoint_compression
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTNormalizedTransverseCharacteristicAnnihilation_normalizedGTTransverseNegativeSector_characteristic_aeval_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseEigenNodeSeparation_negativeStabilizerNode_ne_signedAmbientNode_of_valid_raise
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseRetainedTwoBlockClosure_gtTransverseNegativeSector_relativeCasimir_mem_axis_sup_sector
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTValidTransverseMinorRoots_gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAdjacentCommonInterlacing_gtSelectedPrefixWeight_finiteInterlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAdjacentCommonInterlacing_gtSelectedPrefixWeight_finiteInterlacing_raise
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTValidTransverseSectorFamily_normalizedNegativeSector_canonicalAxis_inner_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTUnconditionalCharacteristicMinor_isometricSector_operator_column_of_mem_axis_sector
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.gtTransverseWallTensorEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_toLinearMap
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_apply
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition.gtFullTransverseInternalEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition.gtFullAxisEmbedding_apply

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
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false))) = 0 := by
  let kappa := gtSelectedPrefixWeight mu
  let hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu :=
    positiveGelfandTsetlinFischerGram (by omega) lam (raiseWeight mu row) hnu
  let hkappa : FiniteInterlacing n mu kappa :=
    gtSelectedPrefixWeight_finiteInterlacing mu (by omega)
      (interlaces_antitone_stabilizer h)
  let hraise : FiniteInterlacing n (raiseWeight mu row) kappa :=
    gtSelectedPrefixWeight_finiteInterlacing_raise
      mu row (by omega) (interlaces_antitone_stabilizer h)
        (interlaces_antitone_stabilizer hnu)
  let A := canonicalGelfandTsetlinAxisIsometry lam mu h hgram
  let B := normalizedGTTransverseNegativeSector
    lam mu kappa row hnu hnuGram hkappa hraise
  let T := gtRelativeCasimir (n := n + 1) lam
  let node := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
    (stabilizerShift (n + 1) mu) (.inr (row, false))
  have horth : A.toLinearMap.adjoint.comp B.toLinearMap = 0 := by
    apply LinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
    rw [LinearMap.adjoint_inner_right]
    exact normalizedNegativeSector_canonicalAxis_inner_eq_zero
      lam mu kappa h hgram row hnu hnuGram hkappa hraise y x
  have hdiag : B.toLinearMap.adjoint.comp (T.comp B.toLinearMap) =
      node • LinearMap.id :=
    normalizedGTTransverseNegativeSector_relativeCasimir_adjoint_compression
      lam mu kappa row hnu hnuGram hkappa hraise
  have hclosed (x : HarmonicYoungSpace (n := n) mu) :
      T (B x) ∈ LinearMap.range A.toLinearMap ⊔
        LinearMap.range B.toLinearMap :=
    gtTransverseNegativeSector_relativeCasimir_mem_axis_sup_sector
      lam mu kappa row h hgram hnu hnuGram hkappa hraise hn x
  let K := A.toLinearMap.adjoint.comp (T.comp B.toLinearMap)
  have hcolumn : T.comp B.toLinearMap = node • B.toLinearMap +
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp K :=
    isometricSector_operator_column_of_mem_axis_sector
      A B T node horth hdiag hclosed
  exact gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
    lam mu h hgram hfinite hn B node K
    (fun x y => normalizedNegativeSector_canonicalAxis_inner_eq_zero
      lam mu kappa h hgram row hnu hnuGram hkappa hraise x y)
    hcolumn
    (fun x => normalizedGTTransverseNegativeSector_characteristic_aeval_eq_zero
      hn lam mu kappa row hnu hnuGram hkappa hraise x)
    (negativeStabilizerNode_ne_signedAmbientNode_of_valid_raise
      lam mu hfinite row hnu)
    p q
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor
