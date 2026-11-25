-- Prove2me | solution 1 for Newton.adjointAction.compose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:49.564611+00:00
-- url     : https://prove2.me/submissions/dfab495d-a554-4fe8-ab9c-02b522e43e4a

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GaugeTransformation
import Theorems.Thm_Newton_adjointAction_one_action
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix


attribute [local simp] Newton.adjointAction.one_action

set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAction
namespace Newton.adjointAction
theorem _root_.solution (g h : SUNGroup N) (A : SuNAlgebra N) :
    adjointAction (g * h) A = adjointAction g (adjointAction h A) := by
  apply SuNAlgebra.ext
  simp only [adjointAction, SUNGroup.mul_matrix, conjTranspose_mul]
  -- (gh) A (gh)† = (gh) A (h† g†) = g (h A h†) g†
  simp only [Matrix.mul_assoc]
end Newton.adjointAction
