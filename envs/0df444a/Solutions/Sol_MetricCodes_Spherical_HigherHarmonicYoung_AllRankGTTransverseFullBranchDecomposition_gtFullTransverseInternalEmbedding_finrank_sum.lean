-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition.gtFullTransverseInternalEmbedding_finrank_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/42e15c80-1423-4a79-9d6c-ae3c67c02708

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
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
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
theorem _root_.solution {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (hdom : Antitone lam) :
    Module.finrank ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam) =
      ∑ mu : FullBranchWeight lam,
        Module.finrank ℝ
          (SpherePacking.Euclidean n ⊗[ℝ]
            HarmonicYoungSpace (n := n) (fullBranchSignature mu)) := by
  rw [Module.finrank_tensorProduct]
  calc
    Module.finrank ℝ (SpherePacking.Euclidean n) *
        Module.finrank ℝ (HarmonicYoungSpace (n := n + 1) lam) =
      Module.finrank ℝ (SpherePacking.Euclidean n) *
        ∑ mu : FullBranchWeight lam,
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n)
              (fullBranchSignature mu)) := by
          congr 1
          convert canonicalFullBranch_finrank_sum_allRank lam hn hdom using 1
          · apply Finset.sum_congr rfl
            intro mu _
            congr 1
    _ = ∑ mu : FullBranchWeight lam,
          Module.finrank ℝ
            (SpherePacking.Euclidean n ⊗[ℝ]
              HarmonicYoungSpace (n := n)
                (fullBranchSignature mu)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro mu _
          symm
          exact Module.finrank_tensorProduct
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
