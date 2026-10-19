-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor.diamondOmittedRows_eq_preceding_union_succeeding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/230ec971-758f-4a40-989b-db96dff9eb32

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
    {r : ℕ} (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (S : Finset (Fin (r + 1))) :
    precedingRows target \ insert pivot S =
      (precedingRows pivot \ precedingDiamondSubset pivot S) ∪
        (diamondSucceedingRows target pivot \
          succeedingDiamondSubset pivot S) := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union,
    mem_precedingRows, mem_diamondSucceedingRows,
    precedingDiamondSubset, succeedingDiamondSubset, Finset.mem_filter]
  constructor
  · rintro ⟨hatarget, hnot⟩
    have hne : a ≠ pivot := by
      intro heq
      exact hnot (Or.inl heq)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hlt, fun ha => hnot (Or.inr ha.1)⟩
    · exact Or.inr ⟨⟨hatarget, hgt⟩, fun ha => hnot (Or.inr ha.1)⟩
  · rintro (⟨halow, hnot⟩ | ⟨⟨hatarget, hahigh⟩, hnot⟩)
    · refine ⟨halow.trans hpivot, ?_⟩
      rintro (heq | haS)
      · exact (ne_of_lt halow) heq
      · exact hnot ⟨haS, halow⟩
    · refine ⟨hatarget, ?_⟩
      rintro (heq | haS)
      · exact (ne_of_gt hahigh) heq
      · exact hnot ⟨haS, hahigh⟩
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
