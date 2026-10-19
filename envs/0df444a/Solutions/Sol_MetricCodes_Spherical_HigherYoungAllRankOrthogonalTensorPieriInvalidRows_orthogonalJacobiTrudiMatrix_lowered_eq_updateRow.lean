-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows.orthogonalJacobiTrudiMatrix_lowered_eq_updateRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/935b8f8d-b8b2-44bd-a16c-e8a7f34b5634

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriCoefficient_orthogonalTensorPieriCoefficient_lower_row
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriCoefficient_orthogonalTensorPieriCoefficient_update_row_ne

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
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i : Fin (r + 1)) (hi : 0 < lam i) :
    orthogonalJacobiTrudiMatrix n (loweredInternalYoungWeight lam i) =
      (orthogonalJacobiTrudiMatrix n lam).updateRow i
        (fun j => orthogonalTensorPieriCoefficient n
          (((lam i : ℤ) - (i.val : ℤ)) - 1) (j.val : ℤ)) := by
  ext k j
  by_cases hk : k = i
  · subst k
    simp [Matrix.updateRow,
      orthogonalTensorPieriCoefficient_lower_row n lam i j hi,
      loweredInternalYoungWeight]
  · simp [Matrix.updateRow, hk, loweredInternalYoungWeight,
      orthogonalTensorPieriCoefficient_update_row_ne n lam k i j
        (lam i - 1) hk]
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
