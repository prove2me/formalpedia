-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.orthogonalJacobiTrudiMatrix_lastRow_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/59bd6d14-36c1-4826-9852-cd628d59f609

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriCoefficient_orthogonalTensorPieriCoefficient_padded_zero_fin
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
    (hzero : lam (Fin.last r) = 0) (j : Fin (r + 1)) :
    orthogonalJacobiTrudiMatrix n lam (Fin.last r) j =
      if j = Fin.last r then 1 else 0 := by
  rw [orthogonalTensorPieriCoefficient_eq_matrix]
  have harg :
      ((lam (Fin.last r) : ℤ) - ((Fin.last r).val : ℤ)) =
        -(r : ℤ) := by simp [hzero]
  rw [harg, orthogonalTensorPieriCoefficient_padded_zero_fin]
  by_cases hj : j = Fin.last r
  · subst j
    simp
  · have hval : j.val ≠ r := by
      intro heq
      apply hj
      apply Fin.ext
      simpa using heq
    simp [hj, hval]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
