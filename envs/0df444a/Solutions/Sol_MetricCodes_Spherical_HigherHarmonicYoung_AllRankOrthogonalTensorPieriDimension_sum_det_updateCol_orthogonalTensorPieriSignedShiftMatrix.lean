-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.sum_det_updateCol_orthogonalTensorPieriSignedShiftMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/dcbadb1d-438b-4ae3-81dd-389bb3dc4234

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_orthogonalTensorPieriSignedShiftMatrix_column
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_det_updateCol_orthogonalTensorPieriNextColumn_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_det_updateCol_orthogonalTensorPieriPrevColumn_eq_zero

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
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    (∑ j : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam).updateCol j
        (fun i => orthogonalTensorPieriSignedShiftMatrix n lam i j)).det) =
      ((orthogonalJacobiTrudiMatrix n lam).updateCol (Fin.last r)
        (orthogonalTensorPieriNextColumn n lam (Fin.last r))).det := by
  classical
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [orthogonalTensorPieriSignedShiftMatrix_column,
      Matrix.det_updateCol_add,
      det_updateCol_orthogonalTensorPieriPrevColumn_eq_zero,
      add_zero]
  · intro j _ hj
    rw [orthogonalTensorPieriSignedShiftMatrix_column,
      Matrix.det_updateCol_add,
      det_updateCol_orthogonalTensorPieriNextColumn_eq_zero n lam j hj,
      det_updateCol_orthogonalTensorPieriPrevColumn_eq_zero,
      add_zero]
  · simp
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
