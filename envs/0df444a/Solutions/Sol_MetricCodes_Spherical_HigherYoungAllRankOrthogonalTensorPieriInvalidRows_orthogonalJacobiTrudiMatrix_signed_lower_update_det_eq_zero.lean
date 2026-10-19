-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows.orthogonalJacobiTrudiMatrix_signed_lower_update_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/ddbc97f4-f3c6-4da0-bd75-37dc29a179b9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriCoefficient_orthogonalTensorPieriCoefficient_padded_zero_pred_fin
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
noncomputable section
set_option autoImplicit false
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
theorem _root_.solution
    {r : ℕ} (n : ℕ) {lam : Fin (r + 1) → ℕ}
    (hlam : Antitone lam) (i : Fin (r + 1)) (hi : lam i = 0) :
    ((orthogonalJacobiTrudiMatrix n lam).updateRow i
      (fun j => orthogonalTensorPieriCoefficient n
        (((lam i : ℤ) - (i.val : ℤ)) - 1) (j.val : ℤ))).det = 0 := by
  classical
  by_cases hilast : i = Fin.last r
  · subst i
    apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last r)
    intro j
    rw [Matrix.updateRow_self]
    simpa [hi] using
      orthogonalTensorPieriCoefficient_padded_zero_pred_fin n r j
  · have hilt : i < Fin.last r := Fin.lt_last_iff_ne_last.mpr hilast
    let next : Fin (r + 1) :=
      ⟨i.val + 1, by have h := hilt; omega⟩
    have hinext : i < next := by
      change i.val < i.val + 1
      omega
    have hnext : lam next = 0 := by
      have h := hlam hinext.le
      omega
    apply Matrix.det_zero_of_row_eq (ne_of_lt hinext)
    funext j
    rw [Matrix.updateRow_self,
      Matrix.updateRow_ne (Ne.symm (ne_of_lt hinext)),
      orthogonalTensorPieriCoefficient_eq_matrix]
    congr 1
    simp [hi, hnext, next]
    push_cast
    ring
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
