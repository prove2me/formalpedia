-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.det_updateCol_orthogonalTensorPieriNextColumn_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/4d12c10c-c67a-4800-946d-4a5ef54421e4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriCoefficient_orthogonalTensorPieriCoefficient_eq_matrix

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
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
theorem _root_.solution
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (j : Fin (r + 1)) (hj : j ≠ Fin.last r) :
    ((orthogonalJacobiTrudiMatrix n lam).updateCol j
      (orthogonalTensorPieriNextColumn n lam j)).det = 0 := by
  have hlt : j.val < r := by
    have h := Fin.lt_last_iff_ne_last.mpr hj
    exact h
  let next : Fin (r + 1) := ⟨j.val + 1, by omega⟩
  have hne : next ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    simp [next] at hv
  have hcol : orthogonalTensorPieriNextColumn n lam j =
      (fun i => orthogonalJacobiTrudiMatrix n lam i next) := by
    funext i
    rw [orthogonalTensorPieriCoefficient_eq_matrix]
    change
      orthogonalTensorPieriCoefficient n
          ((lam i : ℤ) - (i.val : ℤ)) ((j.val : ℤ) + 1) =
        orthogonalTensorPieriCoefficient n
          ((lam i : ℤ) - (i.val : ℤ)) (next.val : ℤ)
    simp [next]
  rw [hcol]
  exact Matrix.det_updateCol_eq_zero hne
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
