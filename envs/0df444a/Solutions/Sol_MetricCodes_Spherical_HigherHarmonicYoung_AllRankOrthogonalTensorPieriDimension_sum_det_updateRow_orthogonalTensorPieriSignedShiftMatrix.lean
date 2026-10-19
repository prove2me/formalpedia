-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.sum_det_updateRow_orthogonalTensorPieriSignedShiftMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/8f7274dc-8979-48da-b138-81b174f30b8d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn_det_updateCol_last_of_lastRow_delta
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_sum_det_updateCol_orthogonalTensorPieriSignedShiftMatrix
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_sum_det_updateRow_eq_sum_det_updateCol
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_orthogonalJacobiTrudiMatrix_lastRow_delta
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_orthogonalTensorPieriNextColumn_last

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
    (hzero : lam (Fin.last r) = 0) :
    (∑ i : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam).updateRow i
        (orthogonalTensorPieriSignedShiftMatrix n lam i)).det) =
      (n : ℤ) * orthogonalJacobiTrudiDimension n lam := by
  calc
    (∑ i : Fin (r + 1),
        ((orthogonalJacobiTrudiMatrix n lam).updateRow i
          (orthogonalTensorPieriSignedShiftMatrix n lam i)).det) =
        ∑ j : Fin (r + 1),
          ((orthogonalJacobiTrudiMatrix n lam).updateCol j
            (fun i => orthogonalTensorPieriSignedShiftMatrix n lam i j)).det :=
      sum_det_updateRow_eq_sum_det_updateCol
        (orthogonalJacobiTrudiMatrix n lam)
        (orthogonalTensorPieriSignedShiftMatrix n lam)
    _ = ((orthogonalJacobiTrudiMatrix n lam).updateCol (Fin.last r)
          (orthogonalTensorPieriNextColumn n lam (Fin.last r))).det :=
      sum_det_updateCol_orthogonalTensorPieriSignedShiftMatrix n lam
    _ = orthogonalTensorPieriNextColumn n lam (Fin.last r)
          (Fin.last r) * (orthogonalJacobiTrudiMatrix n lam).det :=
      det_updateCol_last_of_lastRow_delta
        (orthogonalJacobiTrudiMatrix n lam)
        (orthogonalTensorPieriNextColumn n lam (Fin.last r))
        (orthogonalJacobiTrudiMatrix_lastRow_delta n lam hzero)
    _ = (n : ℤ) * orthogonalJacobiTrudiDimension n lam := by
      rw [orthogonalTensorPieriNextColumn_last n lam hzero]
      rfl
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
