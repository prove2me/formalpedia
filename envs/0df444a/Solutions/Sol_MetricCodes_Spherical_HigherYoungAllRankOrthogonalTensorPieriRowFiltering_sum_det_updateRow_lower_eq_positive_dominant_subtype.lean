-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering.sum_det_updateRow_lower_eq_positive_dominant_subtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/907c06a4-ea72-4a26-b278-f3de76fb8867

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriInvalidRows_orthogonalJacobiTrudiMatrix_lowered_eq_updateRow
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriInvalidRows_orthogonalJacobiTrudiDimension_lowered_eq_zero_of_not_antitone
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriInvalidRows_orthogonalJacobiTrudiMatrix_signed_lower_update_det_eq_zero
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
        (orthogonalTensorPieriLowerRow n lam i)).det) =
      ∑ i : {i : Fin (r + 1) //
        0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)},
        orthogonalJacobiTrudiDimension n
          (loweredInternalYoungWeight lam i.val) := by
  classical
  let P : Fin (r + 1) → Prop :=
    fun i => 0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)
  let f : Fin (r + 1) → ℤ := fun i =>
    ((orthogonalJacobiTrudiMatrix n lam).updateRow i
      (orthogonalTensorPieriLowerRow n lam i)).det
  have hpositive (i : Fin (r + 1)) (hi : 0 < lam i) :
      f i = orthogonalJacobiTrudiDimension n
        (loweredInternalYoungWeight lam i) := by
    dsimp [f]
    unfold orthogonalJacobiTrudiDimension orthogonalTensorPieriLowerRow
    rw [orthogonalJacobiTrudiMatrix_lowered_eq_updateRow n lam i hi]
  have hzero (i : Fin (r + 1)) (hi : ¬ P i) : f i = 0 := by
    by_cases hpos : 0 < lam i
    · have hbad : ¬ Antitone (loweredInternalYoungWeight lam i) := by
        intro hdom
        exact hi ⟨hpos, hdom⟩
      rw [hpositive i hpos]
      exact orthogonalJacobiTrudiDimension_lowered_eq_zero_of_not_antitone
        n hlam i hbad
    · have hweight : lam i = 0 := by omega
      exact orthogonalJacobiTrudiMatrix_signed_lower_update_det_eq_zero
        n hlam i hweight
  change (∑ i : Fin (r + 1), f i) =
    ∑ i : {i : Fin (r + 1) // P i},
      orthogonalJacobiTrudiDimension n
        (loweredInternalYoungWeight lam i.val)
  rw [sum_eq_subtype_of_eq_zero P f hzero]
  apply Finset.sum_congr rfl
  intro i _
  exact hpositive i.val i.property.1
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
