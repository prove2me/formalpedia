-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn.det_updateCol_of_row_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/ff33bf35-6970-4088-9dad-52f9cb951f24

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
noncomputable section
set_option autoImplicit false
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn
theorem _root_.solution
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (i : ι) (v : ι → R)
    (hrow : ∀ j, M i j = if j = i then 1 else 0) :
    (M.updateCol i v).det = v i * M.det := by
  classical
  let residual : ι → R := fun k => v k - v i * M k i
  have hv : v = v i • (fun k => M k i) + residual := by
    funext k
    simp [residual]
  have hzero : (M.updateCol i residual).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    by_cases hji : j = i
    · subst j
      simp [residual, hrow i]
    · simp [Matrix.updateCol, hji, hrow j]
  calc
    (M.updateCol i v).det =
        (M.updateCol i (v i • (fun k => M k i) + residual)).det := by
      exact congrArg (fun w => (M.updateCol i w).det) hv
    _ = (M.updateCol i (v i • (fun k => M k i))).det +
        (M.updateCol i residual).det :=
      Matrix.det_updateCol_add M i _ _
    _ = v i * M.det + (M.updateCol i residual).det := by
      rw [Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]
    _ = v i * M.det := by rw [hzero, add_zero]
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn
