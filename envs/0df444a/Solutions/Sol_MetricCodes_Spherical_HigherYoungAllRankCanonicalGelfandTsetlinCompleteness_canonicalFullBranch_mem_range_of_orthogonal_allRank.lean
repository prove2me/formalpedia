-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness.canonicalFullBranch_mem_range_of_orthogonal_allRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/5df9b7b3-65a4-44ae-a1ec-d4b868fedb3b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalBranchCompleteness_orthogonalBranch_mem_range_of_orthogonal
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranch_finrank_sum_allRank

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
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualBranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
theorem _root_.solution {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (hdom : Antitone lam)
    (horth : ∀ (mu nu : FullBranchWeight lam), mu ≠ nu →
      ∀ (p : HarmonicYoungSpace
          (n := n - 1) (fullBranchSignature mu))
        (q : HarmonicYoungSpace
          (n := n - 1) (fullBranchSignature nu)),
        ⟪canonicalFullBranchFibre lam hn mu p,
          canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0)
    (mu : FullBranchWeight lam) (x : HarmonicYoungSpace (n := n) lam)
    (hx : ∀ (nu : FullBranchWeight lam), nu ≠ mu →
      ∀ q : HarmonicYoungSpace
        (n := n - 1) (fullBranchSignature nu),
        ⟪x, canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0) :
    x ∈ LinearMap.range (canonicalFullBranchFibre lam hn mu).toLinearMap :=
  orthogonalBranch_mem_range_of_orthogonal (canonicalFullBranchFibre lam hn)
    horth (canonicalFullBranch_finrank_sum_allRank lam hn hdom) mu x hx
end MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
