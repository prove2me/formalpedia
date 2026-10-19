-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath.spectralPathCoeff_succ_of_preceding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/1590aacb-3e33-4cfe-8ea2-bd3300f22715

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralPath_spectralPathCoeff_insert
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralPath_spectralPathCoeff_succ_insert_predecessor

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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonLastRoot
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
theorem _root_.solution {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (t : ℝ) (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows a.castSucc) :
    spectralPathCoeff lam a.succ t S =
      (shiftedRowGap lam a.succ a.castSucc + t) *
        spectralPathCoeff lam a.castSucc
          (t + shiftedRowGap lam a.succ a.castSucc + 1) S := by
  have hnot : a.castSucc ∉ S := by
    intro ha
    exact (lt_irrefl a.castSucc)
      ((mem_precedingRows a.castSucc a.castSucc).mp (hS ha))
  have hstep : a.castSucc < a.succ := by
    change a.val < a.val + 1
    omega
  rw [spectralPathCoeff_insert lam a.succ a.castSucc t S hstep hnot,
    spectralPathCoeff_succ_insert_predecessor lam hdom a t S hS]
  ring
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
