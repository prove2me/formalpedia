-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport.polarization_diamondPathOperator_pivot_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/2ab5c38c-09a1-4a63-bdd9-9c277017a16f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondRootCommutator_polarization_axialCoordinate_mul_lowerPolarizationPath_sub
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRootTransport_upperPolarizationPathCommutator_append_pivot

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
    {r n : ℕ} (pivot target : Fin (r + 1)) (hpt : pivot < target)
    (k : Fin n) (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows pivot)
    (p : PolynomialSpace r n) :
    polarization r n target pivot (diamondPathOperator pivot k S p) -
        diamondPathOperator pivot k S
          (polarization r n target pivot p) =
      diamondPathOperator target k S p := by
  classical
  by_cases hnon : S.Nonempty
  · have hstart : polarizationPathStart pivot S < pivot :=
      polarizationPathStart_lt_of_nonempty pivot S hnon hS
    have hstart_ne : pivot ≠ polarizationPathStart pivot S :=
      ne_of_gt hstart
    have hstarts : polarizationPathStart target S =
        polarizationPathStart pivot S := by
      simp [polarizationPathStart, hnon]
    have hlistnon : S.sort (· ≤ ·) ≠ [] := by
      intro h
      have hempty : S = ∅ := by
        simpa using congrArg List.toFinset h
      exact hnon.ne_empty hempty
    have hlist : ∀ a ∈ S.sort (· ≤ ·), a < pivot := by
      intro a ha
      exact (mem_precedingRows a pivot).mp
        (hS ((Finset.mem_sort (· ≤ ·)).mp ha))
    rw [diamondPathOperator_apply, diamondPathOperator_apply,
      polarization_axialCoordinate_mul_lowerPolarizationPath_sub,
      if_neg hstart_ne, zero_add,
      upperPolarizationPathCommutator_append_pivot
        pivot target hpt (S.sort (· ≤ ·)) hlistnon hlist]
    simpa [diamondPathOperator_apply, hstarts]
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
    subst S
    simp only [diamondPathOperator_apply, polarizationPathStart_empty,
      Finset.sort_empty, List.nil_append, lowerPolarizationPath,
      LinearMap.id_apply]
    rw [polarization_mul_euler, polarization_X_euler]
    simp
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
