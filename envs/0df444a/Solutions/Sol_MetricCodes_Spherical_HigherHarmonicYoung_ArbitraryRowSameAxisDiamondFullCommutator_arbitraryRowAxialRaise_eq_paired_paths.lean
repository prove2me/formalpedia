-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator.arbitraryRowAxialRaise_eq_paired_paths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/8203b015-a95c-4a84-a83b-902843a70104

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowFirstAxisIntertwining_sum_powerset_erase_insert

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (hrow : raised < target)
    (k : Fin n) (p : PolynomialSpace r n) :
    arbitraryRowAxialRaise lam target k p =
      ∑ S ∈ ((precedingRows target).erase raised).powerset,
        polarizationPathCoefficient lam target (insert raised S) •
          (diamondPathOperator target k (insert raised S) p -
            shiftedRowGap lam target raised •
              diamondPathOperator target k S p) := by
  classical
  rw [arbitraryRowAxialRaise_apply,
    sum_powerset_erase_insert (precedingRows target) raised
      ((mem_precedingRows raised target).mpr hrow)]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub : S ⊆ (precedingRows target).erase raised :=
    Finset.mem_powerset.mp hS
  have hnot : raised ∉ S := by
    intro h
    exact (Finset.mem_erase.mp (hsub h)).1 rfl
  rw [polarizationPathCoefficient_insert lam target raised S hrow hnot]
  simp only [diamondPathOperator_apply, smul_sub, smul_smul]
  module
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
