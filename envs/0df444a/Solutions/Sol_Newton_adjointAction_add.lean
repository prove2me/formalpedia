-- Prove2me | solution 1 for Newton.adjointAction.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:52.181799+00:00
-- url     : https://prove2.me/submissions/bb075344-2627-4ec1-9d4c-79ecc83ed5d0

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
theorem _root_.solution (g : SUNGroup N) (A B : SuNAlgebra N) :
    adjointAction g (A + B) = adjointAction g A + adjointAction g B := by
  apply SuNAlgebra.ext
  simp only [adjointAction, SuNAlgebra.add_matrix]
  rw [Matrix.mul_add, Matrix.add_mul]
end Newton.adjointAction
