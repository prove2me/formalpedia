-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport.zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/e10d358f-957c-46d9-b840-d2cc7464e738

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (appendZeroWeight lam)))
    (hconj :
      (gtRelativeCasimir (n := n) lam).comp
        (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap =
      (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap.comp
        (gtRelativeCasimir (n := n) (appendZeroWeight lam)))
    (c : ℝ) (p : E)
    (heigen : gtRelativeCasimir (n := n) (appendZeroWeight lam) (A p) =
      c • A p) :
    gtRelativeCasimir (n := n) lam
        (zeroRowTransportPaddedPieriChannel lam A p) =
      c • zeroRowTransportPaddedPieriChannel lam A p := by
  have h := LinearMap.congr_fun hconj (A p)
  change gtRelativeCasimir (n := n) lam
      ((zeroRowTensorIsometryEquiv (n := n) lam).symm (A p)) =
    (zeroRowTensorIsometryEquiv (n := n) lam).symm
      (gtRelativeCasimir (n := n) (appendZeroWeight lam) (A p)) at h
  rw [heigen, map_smul] at h
  exact h
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
