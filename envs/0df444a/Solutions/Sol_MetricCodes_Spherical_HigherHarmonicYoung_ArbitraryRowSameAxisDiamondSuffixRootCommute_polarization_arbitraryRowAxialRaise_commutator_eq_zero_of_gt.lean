-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute.polarization_arbitraryRowAxialRaise_commutator_eq_zero_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/3bf679f3-d32d-471f-b4ec-60be270ebb3c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondRootCommutator_polarization_arbitraryRowAxialRaise_commutator_sum
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixRootCommute_upperPolarizationPathCommutator_eq_zero_of_avoids

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
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1))
    (ha : row < a) (hb : row < b) (k : Fin n)
    (p : PolynomialSpace r n) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) -
      arbitraryRowAxialRaise lam row k (polarization r n a b p) = 0 := by
  classical
  rw [polarization_arbitraryRowAxialRaise_commutator_sum]
  apply Finset.sum_eq_zero
  intro S hS
  have hsub : S ⊆ precedingRows row := Finset.mem_powerset.mp hS
  have hstart : polarizationPathStart row S ≤ row := by
    by_cases hnon : S.Nonempty
    · exact le_of_lt
        (polarizationPathStart_lt_of_nonempty row S hnon hsub)
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
      subst S
      simp
  have hpath :
      ∀ q ∈ ((S.sort (· ≤ ·)) ++ [row]), q ≤ row := by
    intro q hq
    rcases List.mem_append.mp hq with hsorted | hlast
    · exact le_of_lt
        ((mem_precedingRows q row).mp
          (hsub ((Finset.mem_sort (· ≤ ·)).mp hsorted)))
    · have hqrow : q = row := by simpa using hlast
      subst q
      exact le_rfl
  have hnota : a ∉ ((S.sort (· ≤ ·)) ++ [row]) := by
    intro h
    exact (not_lt_of_ge (hpath a h)) ha
  have hnotb : b ∉ ((S.sort (· ≤ ·)) ++ [row]) := by
    intro h
    exact (not_lt_of_ge (hpath b h)) hb
  have hbstart : b ≠ polarizationPathStart row S :=
    ne_of_gt (lt_of_le_of_lt hstart hb)
  rw [if_neg hbstart,
    upperPolarizationPathCommutator_eq_zero_of_avoids
      a b ((S.sort (· ≤ ·)) ++ [row]) hnota hnotb]
  simp
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute
