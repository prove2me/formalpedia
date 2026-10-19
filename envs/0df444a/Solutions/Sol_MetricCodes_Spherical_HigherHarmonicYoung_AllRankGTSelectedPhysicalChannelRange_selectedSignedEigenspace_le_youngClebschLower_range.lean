-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalChannelRange.selectedSignedEigenspace_le_youngClebschLower_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/66c40456-bfd5-48f5-b8cf-12b30df1e9df

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRankBranching_fullBranchOfInterlaces_signature_eq_appendZeroWeight
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCanonicalSelectedBranchRange_orthogonalBranch_range_eq_of_cross_orthogonal_of_equiv
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicInterpolation_signedAmbientCharacteristicNodes_injective
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_raise_channel
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanHodgeSelector_internalRowLowerGramScalar_raiseWeight_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankPaddedLowerClebschIntertwining_normalizedPaddedPieriLower_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_raiseWeight_appendZeroWeight_castSucc
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTInvalidNonterminalProjectorVanishing_paddedPieriSignedChannel_injective
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirCompressedResolvent_gtRelativeCasimir_eigen_inner_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransportedPieriOrthogonality_physicalPaddedPieriChannel_inner_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransportedPieriOrthogonality_physicalPaddedPieriChannel_finrank
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalEigenchannelEigenspace_orthogonalEigenchannel_eigenspace_eq_range_of_finrank
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedPhysicalChannelRange_physicalPaddedPieriChannel_relativeCasimir

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
    {r n : ℕ} (hn : 2 * (r + 2) + 4 ≤ n + 1)
    (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hfinite : FiniteInterlacing (n + 1) low mu)
    (hdom : Antitone low)
    (row : Fin (r + 2))
    (hhigh : Antitone (raiseWeight low row)) :
    Module.End.eigenspace (gtRelativeCasimir (n := n + 1) low)
        (signedNode (HigherChannel.ambientShift (n + 1) low)
          (row, true)) ≤
      LinearMap.range
        (youngClebschLower low (raiseWeight low row)
          (sum_raiseWeight low row) row) := by
  classical
  let padded := appendZeroWeight low
  have hpadded : Antitone padded := appendZeroWeight_antitone low hdom
  have hraised : Antitone (raiseWeight padded row.castSucc) := by
    rw [raiseWeight_appendZeroWeight_castSucc]
    exact appendZeroWeight_antitone (raiseWeight low row) hhigh
  let selected : PaddedPieriChannel padded :=
    Sum.inl ⟨row.castSucc, hraised⟩
  have hselected : paddedPieriSource padded selected =
      appendZeroWeight (raiseWeight low row) :=
    raiseWeight_appendZeroWeight_castSucc low row
  have hpadInter : Interlaces padded (appendZeroWeight mu) := by
    have h := fullBranchSignature_interlaces_appendZeroWeight low
      (fullBranchOfInterlaces mu hfinite.2)
    simpa only [padded, fullBranchOfInterlaces_signature_eq_appendZeroWeight]
      using h
  have hpadFinite : FiniteInterlacing (n + 1) padded
      (appendZeroWeight mu) := ⟨hn, hpadInter⟩
  let F := physicalPaddedPieriChannel hn low hpadded
  let G := normalizedPaddedPieriLower (n := n + 1)
    low hdom row hhigh
  let nodes : PaddedPieriChannel padded → ℝ := fun channel =>
    signedNode (HigherChannel.ambientShift (n + 1) padded)
      (paddedPieriSignedChannel padded channel)
  have hnodes : Function.Injective nodes := by
    intro i j hij
    apply paddedPieriSignedChannel_injective padded
    exact signedAmbientCharacteristicNodes_injective hpadFinite hij
  have horth := physicalPaddedPieriChannel_inner_eq_zero hn low hpadded
  have hdim := physicalPaddedPieriChannel_finrank hn low hpadded
  have hnode :
      signedNode (HigherChannel.ambientShift (n + 1) low) (row, true) =
        nodes selected := by
    change HigherChannel.ambientShift (n + 1) low row =
      HigherChannel.ambientShift (n + 1) (appendZeroWeight low) row.castSucc
    exact (ambientShift_appendZeroWeight_castSucc low row).symm
  have hspectral : Module.End.eigenspace (gtRelativeCasimir low)
      (nodes selected) = LinearMap.range (F selected).toLinearMap := by
    apply orthogonalEigenchannel_eigenspace_eq_range_of_finrank
      nodes hnodes (gtRelativeCasimir low) F horth hdim
    intro channel q
    exact physicalPaddedPieriChannel_relativeCasimir
      hn low hpadded channel q
  have hcross : ∀ other : PaddedPieriChannel padded, other ≠ selected →
      ∀ p : HarmonicYoungSpace (n := n + 1) (raiseWeight low row),
      ∀ q : HarmonicYoungSpace (n := n + 1)
        (paddedPieriSource padded other),
        ⟪G p, F other q⟫_ℝ = 0 := by
    intro other hother p q
    apply gtRelativeCasimir_eigen_inner_eq_zero low (G p) (F other q)
      (signedNode (HigherChannel.ambientShift (n + 1) low) (row, true))
      (nodes other)
    · exact gtRelativeCasimir_raise_channel low row G.toLinearMap
        (normalizedPaddedPieriLower_rotation_intertwine
          low hdom row hhigh) p
    · exact physicalPaddedPieriChannel_relativeCasimir
        hn low hpadded other q
    · intro heq
      rw [hnode] at heq
      exact hother (hnodes heq).symm
  have hGrange : LinearMap.range G.toLinearMap =
      LinearMap.range (F selected).toLinearMap :=
    orthogonalBranch_range_eq_of_cross_orthogonal_of_equiv
      F horth hdim G selected hcross
      (paddedSelectedYoungSourceIsometryEquiv
        low (raiseWeight low row) selected hselected)
  have hGphysical : LinearMap.range G.toLinearMap =
      LinearMap.range
        (youngClebschLower low (raiseWeight low row)
          (sum_raiseWeight low row) row) := by
    dsimp only [G]
    rw [normalizedPaddedPieriLower_toLinearMap, LinearMap.range_smul]
    exact inv_ne_zero
      (Real.sqrt_pos.2
        (internalRowLowerGramScalar_raiseWeight_pos low hdom row)).ne'
  intro v hv
  rw [hnode, hspectral, ← hGrange, hGphysical] at hv
  exact hv
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalChannelRange
