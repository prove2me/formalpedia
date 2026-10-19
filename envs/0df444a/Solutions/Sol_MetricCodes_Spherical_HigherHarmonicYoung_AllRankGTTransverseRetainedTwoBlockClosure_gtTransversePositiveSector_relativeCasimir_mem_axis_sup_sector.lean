-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseRetainedTwoBlockClosure.gtTransversePositiveSector_relativeCasimir_mem_axis_sup_sector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/8786f62b-ad03-44b6-a2a3-0a5cb87d50d9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankSelectedBranchSignature_fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTNormalizedTransverseRotationIntertwining_normalizedGTTransversePositiveSector_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedMuAxisProjectionVanishing_gtFullAxisEmbedding_selected_range_eq_canonicalAxis
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedMuAxisProjectionVanishing_gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTFullTransverseSameSignatureRow_positiveSector_selectedFullTensor_adjoint_eigen
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseWrongBranchCompression_gtFullTransverseEmbedding_normalizedPositiveRelativeCasimir_eq_zero_of_wrong_branch
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalSelectedTwoBlockClosure_gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseSelectedClebschRange_linearIsometry_projection_mem_range_of_adjoint_scalar
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseRetainedTwoBlockClosure_normalizedGTTransversePositiveSector_range_le_selectedFullTransverse

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
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseRetainedTwoBlockClosure
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWrongBranchCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseRetainedTwoBlockClosure
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtRelativeCasimir lam
      (normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram p) ∈
      LinearMap.range
        (canonicalGelfandTsetlinAxisIsometry
          lam mu hmu hmuGram).toLinearMap ⊔
      LinearMap.range
        (normalizedGTTransversePositiveSector
          lam mu nu row hmunu hmu hnu hnuGram).toLinearMap := by
  let hn : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  let A := canonicalGelfandTsetlinAxisIsometry lam mu hmu hmuGram
  let B := normalizedGTTransversePositiveSector
    lam mu nu row hmunu hmu hnu hnuGram
  let S := LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap
  change gtRelativeCasimir lam (B p) ∈ S
  apply gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
    lam hn hmu.antitone_ambient S (gtRelativeCasimir lam (B p))
  · intro branch
    by_cases hs : fullBranchSignature branch = appendZeroWeight mu
    · have hb :=
        (fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
          mu hmu branch).mpr hs
      subst branch
      apply Submodule.mem_sup_left
      change
        gtFullAxisEmbedding lam hn (fullBranchOfInterlaces mu hmu)
          ((gtFullAxisEmbedding lam hn
            (fullBranchOfInterlaces mu hmu)).toLinearMap.adjoint
              (gtRelativeCasimir lam (B p))) ∈
          LinearMap.range A.toLinearMap
      rw [← gtFullAxisEmbedding_selected_range_eq_canonicalAxis
        lam mu hmu hn hmuGram]
      exact ⟨_, rfl⟩
    · have hz :=
        gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
          lam mu hmu hstable branch hs B.toLinearMap
          (normalizedGTTransversePositiveSector_rotation_intertwine
            lam mu nu row hmunu hmu hnu hnuGram) p
      change gtFullAxisEmbedding lam hn branch
        ((gtFullAxisEmbedding lam hn branch).toLinearMap.adjoint
          (gtRelativeCasimir lam (B p))) ∈ S
      change (gtFullAxisEmbedding lam hn branch).toLinearMap.adjoint
        (gtRelativeCasimir lam (B p)) = 0 at hz
      rw [hz, map_zero]
      exact S.zero_mem
  · intro branch
    by_cases hb : branch = fullBranchOfInterlaces nu hnu
    · subst branch
      apply Submodule.mem_sup_right
      apply linearIsometry_projection_mem_range_of_adjoint_scalar
        (gtFullTransverseEmbedding lam hn (fullBranchOfInterlaces nu hnu))
        B.toLinearMap
        (normalizedGTTransversePositiveSector_range_le_selectedFullTransverse
          lam mu nu row hmunu hmu hnu hnuGram hn)
        (gtRelativeCasimir lam (B p)) p
        (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, true)))
      exact positiveSector_selectedFullTensor_adjoint_eigen
        lam mu nu row hmunu hmu hnu hnuGram hn p
    · have hz :=
        gtFullTransverseEmbedding_normalizedPositiveRelativeCasimir_eq_zero_of_wrong_branch
          lam mu nu row hmunu hmu hnu hnuGram hn branch hb p
      change gtFullTransverseEmbedding lam hn branch
        ((gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
          (gtRelativeCasimir lam (B p))) ∈ S
      rw [hz, map_zero]
      exact S.zero_mem
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseRetainedTwoBlockClosure
