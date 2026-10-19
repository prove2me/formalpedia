-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport.polarization_diamondPathOperator_later_target_sub_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/65b904de-2a3a-4824-9675-7e3842ce67de

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondRootCommutator_polarization_axialCoordinate_mul_lowerPolarizationPath_sub
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRootTransport_upperPolarizationPathCommutator_later_target_eq_zero

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
theorem _root_.solution
    {r n : ℕ} (pivot rootTarget target : Fin (r + 1))
    (hroot : pivot < rootTarget) (htarget : pivot < target)
    (k : Fin n) (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows pivot)
    (p : PolynomialSpace r n) :
    polarization r n rootTarget pivot
          (diamondPathOperator target k S p) -
        diamondPathOperator target k S
          (polarization r n rootTarget pivot p) = 0 := by
  classical
  have hstart : pivot ≠ polarizationPathStart target S := by
    by_cases hnon : S.Nonempty
    · have hbefore : polarizationPathStart target S < pivot := by
        rw [polarizationPathStart, dif_pos hnon]
        exact (mem_precedingRows _ pivot).mp
          (hS (Finset.min'_mem S hnon))
      exact ne_of_gt hbefore
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
      simp [hempty, ne_of_lt htarget]
  have hlist : ∀ a ∈ S.sort (· ≤ ·), a < pivot := by
    intro a ha
    exact (mem_precedingRows a pivot).mp
      (hS ((Finset.mem_sort (· ≤ ·)).mp ha))
  rw [diamondPathOperator_apply, diamondPathOperator_apply,
    polarization_axialCoordinate_mul_lowerPolarizationPath_sub,
    if_neg hstart,
    upperPolarizationPathCommutator_later_target_eq_zero
      pivot rootTarget target hroot htarget
      (S.sort (· ≤ ·)) hlist]
  simp
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
