-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.orthogonalJacobiTrudiDimension_tensorPieri
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/5561aaa3-f890-47f4-b9d7-57732bf50ac8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriRowFiltering_sum_det_updateRow_raise_eq_dominant_subtype
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriRowFiltering_sum_det_updateRow_lower_eq_positive_dominant_subtype
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_sum_det_updateRow_orthogonalTensorPieriSignedShiftMatrix

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
    (hdom : Antitone lam) (hzero : lam (Fin.last r) = 0) :
    (∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
      orthogonalJacobiTrudiDimension n (raiseWeight lam i.val)) +
      (∑ i : {i : Fin (r + 1) //
        0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)},
        orthogonalJacobiTrudiDimension n
          (loweredInternalYoungWeight lam i.val)) =
      (n : ℤ) * orthogonalJacobiTrudiDimension n lam := by
  classical
  have hsplit :
      (∑ i : Fin (r + 1),
        ((orthogonalJacobiTrudiMatrix n lam).updateRow i
          (orthogonalTensorPieriSignedShiftMatrix n lam i)).det) =
        (∑ i : Fin (r + 1),
          ((orthogonalJacobiTrudiMatrix n lam).updateRow i
            (orthogonalTensorPieriRaiseRow n lam i)).det) +
        (∑ i : Fin (r + 1),
          ((orthogonalJacobiTrudiMatrix n lam).updateRow i
            (orthogonalTensorPieriLowerRow n lam i)).det) := by
    calc
      (∑ i : Fin (r + 1),
        ((orthogonalJacobiTrudiMatrix n lam).updateRow i
          (orthogonalTensorPieriSignedShiftMatrix n lam i)).det) =
          ∑ i : Fin (r + 1),
            (((orthogonalJacobiTrudiMatrix n lam).updateRow i
              (orthogonalTensorPieriRaiseRow n lam i)).det +
            ((orthogonalJacobiTrudiMatrix n lam).updateRow i
              (orthogonalTensorPieriLowerRow n lam i)).det) := by
        apply Finset.sum_congr rfl
        intro i _
        change
          ((orthogonalJacobiTrudiMatrix n lam).updateRow i
            (orthogonalTensorPieriRaiseRow n lam i +
              orthogonalTensorPieriLowerRow n lam i)).det = _
        exact Matrix.det_updateRow_add _ _ _ _
      _ = _ := by rw [Finset.sum_add_distrib]
  have hraw := sum_det_updateRow_orthogonalTensorPieriSignedShiftMatrix
    n lam hzero
  rw [hsplit,
    sum_det_updateRow_raise_eq_dominant_subtype n lam hdom,
    sum_det_updateRow_lower_eq_positive_dominant_subtype n lam hdom] at hraw
  exact hraw
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
