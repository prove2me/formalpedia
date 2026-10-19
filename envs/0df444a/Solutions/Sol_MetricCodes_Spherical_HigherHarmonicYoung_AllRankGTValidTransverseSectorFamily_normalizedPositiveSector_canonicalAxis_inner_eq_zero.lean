-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily.normalizedPositiveSector_canonicalAxis_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/b5c95cb6-5396-431d-8c74-cbcd2119c5ba

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungMixedGapAxisProbability_normalizedChannelIsometry_adjoint_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTValidTransverseMinorRoots_gtTransversePositiveSector_adjoint_canonicalAxis_eq_zero

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
set_option maxHeartbeats 5000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseMinorRoots
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSignedIndex
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram q⟫_ℝ = 0 := by
  change
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      (normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram).toLinearMap q⟫_ℝ = 0
  rw [← LinearMap.adjoint_inner_left
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram).toLinearMap q]
  unfold normalizedGTTransversePositiveSector
  rw [normalizedChannelIsometry_adjoint_apply,
    gtTransversePositiveSector_adjoint_canonicalAxis_eq_zero
      lam mu nu row hmunu hnu hnuGram hmu hmuGram p,
    smul_zero, inner_zero_left]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily
