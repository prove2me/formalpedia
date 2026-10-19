-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath.spectralPathOperator_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/ce998df8-0ce0-484b-ad31-05a3a64980dd

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralPath_spectralPathCoeff_succ_insert_predecessor
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralPath_spectralPathCoeff_succ_of_preceding
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralPath_diamondPathOperator_insert_predecessor

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
theorem _root_.solution {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (target : Fin (r + 1))
    (k : Fin n) (t : ℝ) :
    spectralPathOperator lam a.succ target k t =
      (shiftedRowGap lam a.succ a.castSucc + t) •
        spectralPathOperator lam a.castSucc target k
          (t + shiftedRowGap lam a.succ a.castSucc + 1) -
      (spectralPathOperator lam a.castSucc a.castSucc k
        (t + shiftedRowGap lam a.succ a.castSucc + 1)).comp
          (polarization r n target a.castSucc) := by
  classical
  apply LinearMap.ext
  intro p
  rw [spectralPathOperator_apply, precedingRows_succ a,
    Finset.sum_powerset_insert (by simp)]
  have hfirst :
      (∑ S ∈ (precedingRows a.castSucc).powerset,
        spectralPathCoeff lam a.succ t S •
          diamondPathOperator target k S p) =
        (shiftedRowGap lam a.succ a.castSucc + t) •
          spectralPathOperator lam a.castSucc target k
            (t + shiftedRowGap lam a.succ a.castSucc + 1) p := by
    rw [spectralPathOperator_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [spectralPathCoeff_succ_of_preceding
      lam hdom a t S (Finset.mem_powerset.mp hS), mul_smul]
  have hsecond :
      (∑ S ∈ (precedingRows a.castSucc).powerset,
        spectralPathCoeff lam a.succ t (insert a.castSucc S) •
          diamondPathOperator target k (insert a.castSucc S) p) =
        -(spectralPathOperator lam a.castSucc a.castSucc k
          (t + shiftedRowGap lam a.succ a.castSucc + 1)
            (polarization r n target a.castSucc p)) := by
    rw [spectralPathOperator_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    rw [spectralPathCoeff_succ_insert_predecessor
      lam hdom a t S (Finset.mem_powerset.mp hS),
      diamondPathOperator_insert_predecessor
        a target k S (Finset.mem_powerset.mp hS)]
    simp
  rw [hfirst, hsecond]
  simp [LinearMap.smul_apply, LinearMap.comp_apply, sub_eq_add_neg]
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
