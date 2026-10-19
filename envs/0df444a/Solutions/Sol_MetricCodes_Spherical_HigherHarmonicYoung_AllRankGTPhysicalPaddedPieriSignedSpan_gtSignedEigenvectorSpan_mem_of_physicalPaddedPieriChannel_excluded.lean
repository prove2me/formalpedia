-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan.gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/89bc72d8-a2d1-47f2-bd59-9aabfe882e9b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCompressedResolventSpectral_gtSignedEigenvectorSpan_mem_of_orthogonalComplete_retained_channels
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirZeroRowTransport_transportedPaddedPieriChannel_eigen_of_retained
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransportedPieriOrthogonality_physicalPaddedPieriChannel_inner_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransportedPieriOrthogonality_physicalPaddedPieriChannel_finrank

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
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan
theorem _root_.solution
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hexcluded :
      ∀ i : PaddedPieriChannel (appendZeroWeight lam),
        ¬ retainedPaddedPieriChannel lam i →
          ∀ q : HarmonicYoungSpace (n := n)
            (paddedPieriSource (appendZeroWeight lam) i),
              ⟪v, physicalPaddedPieriChannel hn lam hdom i q⟫_ℝ = 0) :
    v ∈ gtSignedEigenvectorSpan (n := n) lam := by
  classical
  refine gtSignedEigenvectorSpan_mem_of_orthogonalComplete_retained_channels
    lam
    (fun i : PaddedPieriChannel (appendZeroWeight lam) =>
      HarmonicYoungSpace (n := n)
        (paddedPieriSource (appendZeroWeight lam) i))
    (physicalPaddedPieriChannel hn lam hdom)
    (physicalPaddedPieriChannel_inner_eq_zero hn lam hdom)
    (physicalPaddedPieriChannel_finrank hn lam hdom)
    (retainedPaddedPieriChannel lam) ?_ v hexcluded
  intro i hi
  refine ⟨retainedPaddedPieriSignedNode lam ⟨i, hi⟩, ?_⟩
  intro q
  exact transportedPaddedPieriChannel_eigen_of_retained
    hn lam hdom ⟨i, hi⟩ q
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan
