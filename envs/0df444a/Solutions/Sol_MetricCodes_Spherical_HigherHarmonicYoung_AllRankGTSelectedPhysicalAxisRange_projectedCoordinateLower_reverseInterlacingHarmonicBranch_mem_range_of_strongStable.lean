-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalAxisRange.projectedCoordinateLower_reverseInterlacingHarmonicBranch_mem_range_of_strongStable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/6a18c234-c8c7-47f5-90e6-5264b2625c56

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedPhysicalAxisRange_projectedCoordinateLower_canonicalGelfandTsetlinFibre_mem_range_of_strongStable

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
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (reverseInterlacingHarmonicBranch
          (raiseWeight low row) mu hhigh p) ∈
      LinearMap.range
        (reverseInterlacingHarmonicBranch low mu hlow) := by
  have hstable : 2 * (r + 1) + 2 ≤ n := by omega
  let glow : PositiveGelfandTsetlinFischerGram
    (n := n) low mu hlow :=
      positiveGelfandTsetlinFischerGram hstable low mu hlow
  let ghigh : PositiveGelfandTsetlinFischerGram
    (n := n) (raiseWeight low row) mu hhigh :=
      positiveGelfandTsetlinFischerGram hstable
        (raiseWeight low row) mu hhigh
  let highScale : ℝ := Real.sqrt
    (canonicalGelfandTsetlinFischerGram
      (raiseWeight low row) mu hhigh ghigh)
  have hscale : highScale ≠ 0 :=
    (Real.sqrt_pos.mpr
      (canonicalGelfandTsetlinFischerGram_pos
        (raiseWeight low row) mu hhigh ghigh)).ne'
  have hinput :
      canonicalGelfandTsetlinFibre
          (raiseWeight low row) mu hhigh ghigh
          (highScale • p) =
        reverseInterlacingHarmonicBranch
          (raiseWeight low row) mu hhigh p := by
    simp [canonicalGelfandTsetlinFibre_apply, map_smul,
      smul_smul, highScale, hscale]
  have hrange :=
    projectedCoordinateLower_canonicalGelfandTsetlinFibre_mem_range_of_strongStable
      low mu row hnstrong hlow hhigh glow ghigh (highScale • p)
  rw [hinput] at hrange
  obtain ⟨q, hq⟩ := hrange
  refine ⟨(Real.sqrt
    (canonicalGelfandTsetlinFischerGram low mu hlow glow))⁻¹ • q, ?_⟩
  simpa [canonicalGelfandTsetlinFibre_apply, map_smul] using hq
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalAxisRange
