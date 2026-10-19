-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.det_updateCol_orthogonalTensorPieriPrevColumn_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/0e2b9128-8879-4070-b7bb-8b08c4481572

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
    (j : Fin (r + 1)) :
    ((orthogonalJacobiTrudiMatrix n lam).updateCol j
      (orthogonalTensorPieriPrevColumn n lam j)).det = 0 := by
  by_cases hj : j.val = 0
  · apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    simp [orthogonalTensorPieriPrevColumn, hj,
      orthogonalTensorPieriCoefficient_neg_one]
  · have hpositive : 0 < j.val := Nat.pos_of_ne_zero hj
    let prev : Fin (r + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hne : prev ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      simp [prev] at hv
      omega
    have hcol : orthogonalTensorPieriPrevColumn n lam j =
        (fun i => orthogonalJacobiTrudiMatrix n lam i prev) := by
      funext i
      rw [orthogonalTensorPieriCoefficient_eq_matrix]
      change
        orthogonalTensorPieriCoefficient n
            ((lam i : ℤ) - (i.val : ℤ)) ((j.val : ℤ) - 1) =
          orthogonalTensorPieriCoefficient n
            ((lam i : ℤ) - (i.val : ℤ)) (prev.val : ℤ)
      congr 1
      simp [prev, Nat.cast_sub (show 1 ≤ j.val by omega)]
    rw [hcol]
    exact Matrix.det_updateCol_eq_zero hne
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
