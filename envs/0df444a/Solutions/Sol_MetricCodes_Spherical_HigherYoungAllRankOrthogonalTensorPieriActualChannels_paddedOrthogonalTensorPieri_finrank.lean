-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels.paddedOrthogonalTensorPieri_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/4e9a5cfd-0458-47c2-b10d-a9867cd62e10

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_finrank_harmonicYoung_tensorPieri

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
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTensorPieriNormalizedChannels
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
theorem _root_.solution
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (hzero : target (Fin.last r) = 0) :
    n * Module.finrank ℝ (HarmonicYoungSpace (n := n) target) =
      ∑ i : PaddedPieriChannel target,
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n) (paddedPieriSource target i)) := by
  change
    n * Module.finrank ℝ (HarmonicYoungSpace (n := n) target) =
      ∑ i : PaddedPieriRaiseRow target ⊕ PaddedPieriLowerRow target,
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n) (paddedPieriSource target i))
  rw [Fintype.sum_sum_type]
  exact (finrank_harmonicYoung_tensorPieri hn target hdom hzero).symm
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
