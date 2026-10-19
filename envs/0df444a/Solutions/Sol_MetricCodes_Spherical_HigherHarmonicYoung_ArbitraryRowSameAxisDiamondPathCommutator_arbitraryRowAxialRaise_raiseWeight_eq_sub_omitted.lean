-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator.arbitraryRowAxialRaise_raiseWeight_eq_sub_omitted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/6790e170-833e-49df-a82c-724832c49db4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowFirstAxisIntertwining_sum_powerset_erase_insert
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondGapShift_polarizationPathCoefficient_raiseWeight_of_mem
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondGapShift_polarizationPathCoefficient_raiseWeight_of_not_mem

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (hrow : raised < target)
    (hdom : lam target ≤ lam raised) (k : Fin n) :
    arbitraryRowAxialRaise (raiseWeight lam raised) target k =
      arbitraryRowAxialRaise lam target k -
        diamondOmittedRowOperator lam target raised k := by
  classical
  apply LinearMap.ext
  intro p
  rw [LinearMap.sub_apply, arbitraryRowAxialRaise_apply,
    arbitraryRowAxialRaise_apply, diamondOmittedRowOperator_apply]
  have hmem : raised ∈ precedingRows target :=
    (mem_precedingRows raised target).mpr hrow
  rw [sum_powerset_erase_insert (precedingRows target) raised hmem,
    sum_powerset_erase_insert (precedingRows target) raised hmem,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub : S ⊆ (precedingRows target).erase raised :=
    Finset.mem_powerset.mp hS
  have hnot : raised ∉ S := by
    intro h
    exact (Finset.mem_erase.mp (hsub h)).1 rfl
  rw [polarizationPathCoefficient_raiseWeight_of_not_mem
    lam target raised hrow hdom S hnot,
    polarizationPathCoefficient_raiseWeight_of_mem
      lam target raised (ne_of_gt hrow)
      (insert raised S) (Finset.mem_insert_self _ _), sub_smul]
  abel
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
