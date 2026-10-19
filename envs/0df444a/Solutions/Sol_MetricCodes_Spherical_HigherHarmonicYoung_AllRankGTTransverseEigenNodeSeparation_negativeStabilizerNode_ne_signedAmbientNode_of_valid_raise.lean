-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation.negativeStabilizerNode_ne_signedAmbientNode_of_valid_raise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/5541b1b8-3397-453b-9778-dd170cc626aa

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
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1))
    (hraise : Interlaces lam (raiseWeight mu row))
    (channel : Fin (r + 2) × Bool) :
    gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false)) ≠
      signedNode (ambientShift (n + 1) lam) channel := by
  have hweight : mu row < lam row.castSucc := by
    have hh := (hraise row).1
    simpa [raiseWeight] using hh
  have hweightR : (mu row : ℝ) < (lam row.castSucc : ℝ) := by
    exact_mod_cast hweight
  have hupper :
      stabilizerShift (n + 1) mu row + 1 / 2 <
        ambientShift (n + 1) lam row.castSucc := by
    simp only [stabilizerShift, ambientShift, Fin.val_castSucc,
      Nat.cast_add, Nat.cast_one]
    linarith
  have hlower :
      ambientShift (n + 1) lam row.succ <
        stabilizerShift (n + 1) mu row + 1 / 2 := by
    linarith [hfinite.stabilizerShift_ge_succ row]
  rcases channel with ⟨j, sign⟩
  cases sign
  · simp [gtStabilizerArrowheadNode_neg, signedNode]
    intro heq
    have hcoord :
        stabilizerShift (n + 1) mu row + 1 / 2 =
          ambientShift (n + 1) lam j := by linarith
    by_cases hji : j ≤ row.castSucc
    · have hmono := hfinite.ambientShift_strictAnti.antitone hji
      linarith
    · have hij : row.succ ≤ j := by
        have hlt : row.castSucc < j := lt_of_not_ge hji
        apply Fin.le_iff_val_le_val.mpr
        have hv : row.val < j.val := hlt
        exact Nat.succ_le_of_lt hv
      have hmono := hfinite.ambientShift_strictAnti.antitone hij
      linarith
  · simp [gtStabilizerArrowheadNode_neg, signedNode]
    have hM := hfinite.stabilizerShift_pos row
    have hL := hfinite.ambientShift_pos j
    linarith
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation
