-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering.sum_det_updateRow_raise_eq_dominant_subtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/6e605060-2266-435f-bf6d-5a4aded8e4ac

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriInvalidRows_orthogonalJacobiTrudiMatrix_raiseWeight_eq_updateRow
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriInvalidRows_orthogonalJacobiTrudiDimension_raiseWeight_eq_zero_of_not_antitone
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriRowFiltering_sum_eq_subtype_of_eq_zero

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
open scoped BigOperators
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
theorem _root_.solution
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (hlam : Antitone lam) :
    (∑ i : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam).updateRow i
        (orthogonalTensorPieriRaiseRow n lam i)).det) =
      ∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
        orthogonalJacobiTrudiDimension n (raiseWeight lam i.val) := by
  classical
  have hterm (i : Fin (r + 1)) :
      ((orthogonalJacobiTrudiMatrix n lam).updateRow i
        (orthogonalTensorPieriRaiseRow n lam i)).det =
        orthogonalJacobiTrudiDimension n (raiseWeight lam i) := by
    unfold orthogonalJacobiTrudiDimension orthogonalTensorPieriRaiseRow
    rw [orthogonalJacobiTrudiMatrix_raiseWeight_eq_updateRow]
  calc
    (∑ i : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam).updateRow i
        (orthogonalTensorPieriRaiseRow n lam i)).det) =
        ∑ i : Fin (r + 1),
          orthogonalJacobiTrudiDimension n (raiseWeight lam i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterm i
    _ = ∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
          orthogonalJacobiTrudiDimension n (raiseWeight lam i.val) := by
            apply sum_eq_subtype_of_eq_zero
              (fun i : Fin (r + 1) => Antitone (raiseWeight lam i))
            intro i hbad
            exact orthogonalJacobiTrudiDimension_raiseWeight_eq_zero_of_not_antitone
              n hlam i hbad
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
