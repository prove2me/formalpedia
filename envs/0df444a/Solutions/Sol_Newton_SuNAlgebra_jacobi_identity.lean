-- Prove2me | solution 1 for Newton.SuNAlgebra.jacobi_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:11:51.641318+00:00
-- url     : https://prove2.me/submissions/038f677f-15af-49ab-93c6-c10b6c5f7cf3

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
theorem _root_.solution (A B C : SuNAlgebra N) :
    ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = (0 : SuNAlgebra N) :=
  lie_jacobi A B C
end SuNAlgebra
end Newton
