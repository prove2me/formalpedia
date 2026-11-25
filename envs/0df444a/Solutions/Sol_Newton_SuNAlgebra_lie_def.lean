-- Prove2me | solution 1 for Newton.SuNAlgebra.lie_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:30:52.956833+00:00
-- url     : https://prove2.me/submissions/d1e6a2e7-68d7-43c8-9310-30cee4ef99a6

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
namespace SuNAlgebra
theorem _root_.solution (A B : SuNAlgebra N) :
    (⁅A, B⁆ : SuNAlgebra N).matrix = A.matrix * B.matrix - B.matrix * A.matrix :=
  Ring.lie_def A.matrix B.matrix
end SuNAlgebra
end Newton
