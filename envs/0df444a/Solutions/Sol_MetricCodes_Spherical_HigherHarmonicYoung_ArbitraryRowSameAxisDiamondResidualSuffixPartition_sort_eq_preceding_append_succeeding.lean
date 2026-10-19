-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition.sort_eq_preceding_append_succeeding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/42243fef-6503-43ef-ae3c-8171de4278c3

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
theorem _root_.solution
    {r : ℕ} (pivot : Fin (r + 1))
    (S : Finset (Fin (r + 1))) (hpivot : pivot ∉ S) :
    S.sort (· ≤ ·) =
      (precedingDiamondSubset pivot S).sort (· ≤ ·) ++
        (succeedingDiamondSubset pivot S).sort (· ≤ ·) := by
  classical
  let L := precedingDiamondSubset pivot S
  let U := succeedingDiamondSubset pivot S
  let path := L.sort (· ≤ ·) ++ U.sort (· ≤ ·)
  have hnodup : path.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.sort_nodup L (· ≤ ·),
      Finset.sort_nodup U (· ≤ ·), ?_⟩
    intro a ha b hb hab
    have haL : a ∈ L := (Finset.mem_sort (· ≤ ·)).mp ha
    have hbU : b ∈ U := (Finset.mem_sort (· ≤ ·)).mp hb
    have halow : a < pivot := (Finset.mem_filter.mp haL).2
    have hbhigh : pivot < b := (Finset.mem_filter.mp hbU).2
    exact (ne_of_lt (halow.trans hbhigh)) hab
  have hsorted : path.Pairwise (· ≤ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨Finset.pairwise_sort L (· ≤ ·),
      Finset.pairwise_sort U (· ≤ ·), ?_⟩
    intro a ha b hb
    have haL : a ∈ L := (Finset.mem_sort (· ≤ ·)).mp ha
    have hbU : b ∈ U := (Finset.mem_sort (· ≤ ·)).mp hb
    exact le_of_lt
      ((Finset.mem_filter.mp haL).2.trans
        (Finset.mem_filter.mp hbU).2)
  have hfin : path.toFinset = S := by
    ext a
    simp only [path, List.toFinset_append,
      List.mem_toFinset, Finset.mem_union, Finset.mem_sort,
      L, U, precedingDiamondSubset, succeedingDiamondSubset,
      Finset.mem_filter]
    constructor
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩)
      · exact ha
      · exact ha
    · intro ha
      have hne : a ≠ pivot := by
        intro heq
        subst a
        exact hpivot ha
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨ha, hlt⟩
      · exact Or.inr ⟨ha, hgt⟩
  have hcanonical := (List.toFinset_sort (r := (· ≤ ·)) hnodup).mpr hsorted
  simpa [hfin, path, L, U] using hcanonical
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
