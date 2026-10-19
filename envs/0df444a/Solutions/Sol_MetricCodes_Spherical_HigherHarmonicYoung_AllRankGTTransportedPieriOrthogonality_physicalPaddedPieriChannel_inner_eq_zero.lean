-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality.physicalPaddedPieriChannel_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/ed0d17d2-745b-4194-af3e-1452e9a6c8eb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity_paddedPieriSource_injective
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity_paddedPieriSource_isOneBoxNeighbor
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriActualChannels_paddedOrthogonalTensorPieriChannel_rotation_intertwine

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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
theorem _root_.solution {r n : ℕ}
    (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (i j : PaddedPieriChannel (appendZeroWeight lam)) (hij : i ≠ j)
    (p : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight lam) i))
    (q : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight lam) j)) :
    ⟪physicalPaddedPieriChannel hn lam hdom i p,
      physicalPaddedPieriChannel hn lam hdom j q⟫_ℝ = 0 := by
  change
    ⟪(zeroRowTensorIsometryEquiv (n := n) lam).symm
        (paddedOrthogonalTensorPieriChannel hn
          (appendZeroWeight lam) hdom i p),
      (zeroRowTensorIsometryEquiv (n := n) lam).symm
        (paddedOrthogonalTensorPieriChannel hn
          (appendZeroWeight lam) hdom j q)⟫_ℝ = 0
  rw [(zeroRowTensorIsometryEquiv (n := n) lam).symm.inner_map_map]
  have hne :
      paddedPieriSource (appendZeroWeight lam) i ≠
        paddedPieriSource (appendZeroWeight lam) j := by
    intro heq
    exact hij (paddedPieriSource_injective (appendZeroWeight lam) heq)
  have hzero := allRankYoungChannel_crossGram_eq_zero_of_oneBoxNeighbors
    (by omega) (appendZeroWeight lam)
    (paddedPieriSource (appendZeroWeight lam) i)
    (paddedPieriSource (appendZeroWeight lam) j)
    hdom
    (paddedPieriSource_isOneBoxNeighbor (appendZeroWeight lam) i)
    (paddedPieriSource_isOneBoxNeighbor (appendZeroWeight lam) j)
    hne
    (paddedOrthogonalTensorPieriChannel hn
      (appendZeroWeight lam) hdom i).toLinearMap
    (paddedOrthogonalTensorPieriChannel hn
      (appendZeroWeight lam) hdom j).toLinearMap
    (paddedOrthogonalTensorPieriChannel_rotation_intertwine hn
      (appendZeroWeight lam) hdom i)
    (paddedOrthogonalTensorPieriChannel_rotation_intertwine hn
      (appendZeroWeight lam) hdom j)
  calc
    ⟪paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom i p,
      paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom j q⟫_ℝ =
        ⟪p, (paddedOrthogonalTensorPieriChannel hn
          (appendZeroWeight lam) hdom i).toLinearMap.adjoint
            (paddedOrthogonalTensorPieriChannel hn
              (appendZeroWeight lam) hdom j q)⟫_ℝ :=
      (LinearMap.adjoint_inner_right
        (paddedOrthogonalTensorPieriChannel hn
          (appendZeroWeight lam) hdom i).toLinearMap p
        (paddedOrthogonalTensorPieriChannel hn
          (appendZeroWeight lam) hdom j q)).symm
    _ = 0 := by
      have hz :
          (paddedOrthogonalTensorPieriChannel hn
            (appendZeroWeight lam) hdom i).toLinearMap.adjoint
              (paddedOrthogonalTensorPieriChannel hn
                (appendZeroWeight lam) hdom j q) = 0 := by
        simpa using LinearMap.congr_fun hzero q
      rw [hz]
      exact @inner_zero_right ℝ
        (HarmonicYoungSpace (n := n)
          (paddedPieriSource (appendZeroWeight lam) i)) _ _ _ p
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
