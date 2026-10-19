-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.sum_det_updateRow_eq_sum_det_updateCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/4dd6ea77-85b3-42bc-b367-3a7df7d50eab

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M B : Matrix ι ι R) :
    (∑ i : ι, (M.updateRow i (B i)).det) =
      ∑ j : ι, (M.updateCol j (fun i => B i j)).det := by
  classical
  calc
    (∑ i : ι, (M.updateRow i (B i)).det) =
        ∑ i : ι, ∑ j : ι, M.adjugate j i * B i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Matrix.cramer_transpose_apply M (B i) i,
        Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mulVec, dotProduct, ← Matrix.adjugate_transpose]
    _ = ∑ j : ι, ∑ i : ι, M.adjugate j i * B i j := by
      rw [Finset.sum_comm]
    _ = ∑ j : ι, (M.updateCol j (fun i => B i j)).det := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Matrix.cramer_apply M (fun i => B i j) j,
        Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mulVec, dotProduct]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
