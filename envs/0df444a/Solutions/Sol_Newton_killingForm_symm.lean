-- Prove2me | solution 1 for Newton.killingForm_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:30.998514+00:00
-- url     : https://prove2.me/submissions/0912309e-c306-4d08-913f-56552a0a54f7

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Definitions.Def_Newton_Gauge_LieAlgebra

set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
namespace Newton
theorem _root_.solution [DecidableEq (Fin N)] (A B : SuNAlgebra N) :
    killingForm A B = killingForm B A := by
  unfold killingForm
  exact trace_mul_comm A.matrix B.matrix
end Newton
