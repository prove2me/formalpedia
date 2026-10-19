-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization.normalizedGTTransverseWallSector_range_le_fullTransverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/87890c54-a7f0-494d-aed8-8cf5a6de9d40

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallFullTransverseFactorization_gtTransverseWallTensorEmbedding_range_eq_fullTransverse
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_apply

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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    LinearMap.range
        (normalizedGTTransverseWallSector
          lam mu h hn hlast).toLinearMap ≤
      LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (gtWallFullBranch lam mu h hlast)).toLinearMap := by
  rw [← gtTransverseWallTensorEmbedding_range_eq_fullTransverse
    lam mu h hn hlast]
  rintro _ ⟨p, rfl⟩
  change normalizedGTTransverseWallSector lam mu h hn hlast p ∈ _
  rw [normalizedGTTransverseWallSector_apply]
  change
    (Real.sqrt (MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorGram.gtWallSectorGram n mu))⁻¹ •
      (gtTransverseWallTensorEmbedding lam mu h hn hlast)
        ((youngClebschRaise
          (raiseWeight
            (appendZeroWeight mu)
            (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight
            (appendZeroWeight mu)
            (Fin.last (r + 1)))
          (Fin.last (r + 1)))
            ((appendZeroRowIsometryEquiv mu) p)) ∈ _
  exact Submodule.smul_mem _ _ ⟨_, rfl⟩
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization
