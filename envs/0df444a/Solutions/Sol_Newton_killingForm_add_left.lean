-- Prove2me | solution 1 for Newton.killingForm_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:36.113835+00:00
-- url     : https://prove2.me/submissions/f19462fe-2d58-43c3-b24c-b702e677de8d

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Definitions.Def_Newton_Gauge_LieAlgebra
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix

set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
namespace Newton
theorem _root_.solution [DecidableEq (Fin N)] (A B C : SuNAlgebra N) :
    killingForm (A + B) C = killingForm A C + killingForm B C := by
  unfold killingForm
  simp only [SuNAlgebra.add_matrix, add_mul, trace_add]
end Newton
