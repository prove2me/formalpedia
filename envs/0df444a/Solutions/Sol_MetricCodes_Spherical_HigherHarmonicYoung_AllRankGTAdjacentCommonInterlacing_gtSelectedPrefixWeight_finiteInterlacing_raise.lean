-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing.gtSelectedPrefixWeight_finiteInterlacing_raise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/666f7951-3bca-4b4f-a1a6-bd1955088521

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.gtTransverseWallTensorEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_toLinearMap
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_apply
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition.gtFullTransverseInternalEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition.gtFullAxisEmbedding_apply

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
set_option autoImplicit false
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
theorem _root_.solution
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hn : 2 * r + 4 ≤ n)
    (hdom : Antitone mu)
    (hraiseDom : Antitone (raiseWeight mu row)) :
    FiniteInterlacing n (raiseWeight mu row)
      (gtSelectedPrefixWeight mu) := by
  refine ⟨hn, ?_⟩
  intro j
  constructor
  · change mu j.castSucc ≤ raiseWeight mu row j.castSucc
    by_cases hrow : j.castSucc = row
    · subst row
      simp [raiseWeight]
    · simp [raiseWeight, hrow]
  · by_cases hrow : j.succ = row
    · have hne : j.castSucc ≠ row := by
        intro heq
        have hlt : j.castSucc < j.succ :=
          Fin.castSucc_lt_succ_iff.mpr le_rfl
        rw [heq, hrow] at hlt
        exact (lt_irrefl _ hlt)
      have hle := hraiseDom (Fin.castSucc_le_succ j)
      simpa [gtSelectedPrefixWeight, raiseWeight, hne, hrow] using hle
    · change raiseWeight mu row j.succ ≤ mu j.castSucc
      simpa [raiseWeight, hrow] using hdom (Fin.castSucc_le_succ j)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
