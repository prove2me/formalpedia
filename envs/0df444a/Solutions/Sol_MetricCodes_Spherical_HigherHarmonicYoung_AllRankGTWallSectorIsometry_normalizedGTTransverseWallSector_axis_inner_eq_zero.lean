-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_axis_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/7f234fa3-1aea-45f9-837d-0eac13a4df28

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungMixedGapAxisProbability_normalizedChannelIsometry_adjoint_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallSector_axis_inner_eq_zero

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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪normalizedGTTransverseWallSector lam mu h hn hlast p,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ = 0 := by
  change
    ⟪(normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap p,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ = 0
  rw [← LinearMap.adjoint_inner_right
    (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap p]
  unfold normalizedGTTransverseWallSector
  rw [normalizedChannelIsometry_adjoint_apply]
  have hraw :
      (gtTransverseWallSector lam mu h hn hlast).adjoint
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram q) = 0 := by
    apply ext_inner_left ℝ
    intro x
    rw [inner_zero_right, LinearMap.adjoint_inner_right]
    exact gtTransverseWallSector_axis_inner_eq_zero
      lam mu h hn hlast hgram x q
  rw [hraw, smul_zero, inner_zero_right]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
