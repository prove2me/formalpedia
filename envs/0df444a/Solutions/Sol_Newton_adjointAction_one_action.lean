-- Prove2me | solution 1 for Newton.adjointAction.one_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:43:03.576379+00:00
-- url     : https://prove2.me/submissions/55e2da21-c524-44eb-a79f-9e570c475b87

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GaugeTransformation
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix



set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAction
namespace Newton.adjointAction
theorem _root_.solution (A : SuNAlgebra N) : adjointAction (1 : SUNGroup N) A = A := by
  apply SuNAlgebra.ext
  simp [adjointAction, conjTranspose_one]
end Newton.adjointAction
