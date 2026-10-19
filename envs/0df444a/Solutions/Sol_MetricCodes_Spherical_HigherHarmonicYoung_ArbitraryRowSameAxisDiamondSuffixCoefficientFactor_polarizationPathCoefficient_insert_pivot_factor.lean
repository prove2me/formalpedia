-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor.polarizationPathCoefficient_insert_pivot_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/aab2d27e-96b8-4dc2-be40-8ae381d73c95

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixCoefficientFactor_diamondSubset_eq_preceding_union_succeeding
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixCoefficientFactor_diamondOmittedRows_eq_preceding_union_succeeding
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixCoefficientFactor_shiftedRowGap_target_eq_pivot_add_spectralShift

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
theorem _root_.solution
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (S : Finset (Fin (r + 1))) (hS : pivot ∉ S) :
    polarizationPathCoefficient lam target (insert pivot S) =
      -upperDiamondPathCoefficient lam target pivot S *
        spectralPathCoeff lam pivot
          (shiftedRowGap lam target pivot + 1)
          (precedingDiamondSubset pivot S) := by
  classical
  let lower := precedingDiamondSubset pivot S
  let upper := succeedingDiamondSubset pivot S
  have hdisjoint : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (not_lt_of_ge (Finset.mem_filter.mp hb).2.le)
      (Finset.mem_filter.mp ha).2
  have hcard : S.card = lower.card + upper.card := by
    rw [diamondSubset_eq_preceding_union_succeeding pivot S hS,
      Finset.card_union_of_disjoint hdisjoint]
  have hblocks :
      Disjoint (precedingRows pivot \ lower)
        (diamondSucceedingRows target pivot \ upper) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have halow : a < pivot :=
      (mem_precedingRows a pivot).mp (Finset.mem_sdiff.mp ha).1
    have hahigh : pivot < a :=
      (mem_diamondSucceedingRows target pivot a).mp
        (Finset.mem_sdiff.mp hb).1 |>.2
    exact (not_lt_of_ge hahigh.le) halow
  have hprod :
      (∏ a ∈ precedingRows target \ insert pivot S,
        shiftedRowGap lam target a) =
        (∏ a ∈ precedingRows pivot \ lower,
          (shiftedRowGap lam pivot a +
            (shiftedRowGap lam target pivot + 1))) *
          (∏ a ∈ diamondSucceedingRows target pivot \ upper,
            shiftedRowGap lam target a) := by
    rw [diamondOmittedRows_eq_preceding_union_succeeding
      target pivot hpivot S, Finset.prod_union hblocks]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    exact shiftedRowGap_target_eq_pivot_add_spectralShift
      lam hdom target pivot a hpivot
        ((mem_precedingRows a pivot).mp (Finset.mem_sdiff.mp ha).1)
  unfold polarizationPathCoefficient upperDiamondPathCoefficient spectralPathCoeff
  rw [Finset.card_insert_of_notMem hS, hcard, pow_add, pow_add, hprod]
  ring
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
