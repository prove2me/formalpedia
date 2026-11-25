-- Prove2me | solution 1 for Newton.adjointAction.zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:47:04.692703+00:00
-- url     : https://prove2.me/submissions/03d9bb4c-6b5f-42c5-9816-cf96359c9211

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
theorem _root_.solution (g : SUNGroup N) : adjointAction g (0 : SuNAlgebra N) = 0 := by
  apply SuNAlgebra.ext
  simp [adjointAction]
end Newton.adjointAction
