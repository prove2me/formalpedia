-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalAxisRange.projectedCoordinateLower_canonicalGelfandTsetlinFibre_mem_range_of_strongStable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/31039a6e-1527-406e-9e12-d230904abc14

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranchFibre_orthogonal
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranch_mem_range_of_orthogonal_allRank
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram_canonicalBranchProjectedLower_orthogonal_of_ne_selected
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCanonicalSelectedBranchRange_canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch

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
set_option maxHeartbeats 1800000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalAxisRange
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalForwardAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalAxisRange
theorem _root_.solution
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hnstrong : 2 * (r + 1) + 5 ≤ n + 1)
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hlowGram : PositiveGelfandTsetlinFischerGram
      (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight low row) mu hhigh)
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (canonicalGelfandTsetlinFibre
          (raiseWeight low row) mu hhigh hhighGram p) ∈
      LinearMap.range
        (canonicalGelfandTsetlinFibre low mu hlow hlowGram).toLinearMap := by
  let selected : FullBranchWeight low := fullBranchOfInterlaces mu hlow
  have hdom : Antitone low := hlow.antitone_ambient
  rw [canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
    low mu hlow hnstrong hdom hlowGram]
  apply canonicalFullBranch_mem_range_of_orthogonal_allRank
    low hnstrong hdom
    (canonicalFullBranchFibre_orthogonal low hnstrong) selected
  intro nu hnu q
  exact canonicalBranchProjectedLower_orthogonal_of_ne_selected
    low (raiseWeight low row) mu hlow hhigh
    (sum_raiseWeight low row) row hnstrong nu hnu p q
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalAxisRange
