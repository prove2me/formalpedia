-- Prove2me | solution 1 for Newton.killingForm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:44.773848+00:00
-- url     : https://prove2.me/submissions/448345c1-c7dc-4e9d-b3d2-33797813fe69

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
    killingForm A (B + C) = killingForm A B + killingForm A C := by
  unfold killingForm
  simp only [SuNAlgebra.add_matrix, mul_add, trace_add]
end Newton
