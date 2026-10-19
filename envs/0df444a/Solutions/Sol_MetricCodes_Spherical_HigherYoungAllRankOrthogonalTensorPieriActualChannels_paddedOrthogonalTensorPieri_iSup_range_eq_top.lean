-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels.paddedOrthogonalTensorPieri_iSup_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/77ae9114-99e8-4d9a-b818-b62036850329

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity_paddedPieriSource_injective
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity_paddedPieriSource_isOneBoxNeighbor
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankTensorClebschCompleteness_actualTensorClebsch_iSup_range_eq_top_of_finrank
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriActualChannels_paddedOrthogonalTensorPieriChannel_rotation_intertwine
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriActualChannels_paddedOrthogonalTensorPieri_finrank

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
    (⨆ i : PaddedPieriChannel target,
      LinearMap.range
        (paddedOrthogonalTensorPieriChannel hn target hdom i).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) target)) := by
  apply actualTensorClebsch_iSup_range_eq_top_of_finrank
    (by omega) target hdom (paddedPieriSource target)
    (paddedPieriSource_isOneBoxNeighbor target)
    (paddedPieriSource_injective target)
    (paddedOrthogonalTensorPieriChannel hn target hdom)
    (paddedOrthogonalTensorPieriChannel_rotation_intertwine hn target hdom)
  exact paddedOrthogonalTensorPieri_finrank hn target hdom hzero
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
