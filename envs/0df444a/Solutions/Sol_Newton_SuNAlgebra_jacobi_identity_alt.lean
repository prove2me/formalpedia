-- Prove2me | solution 1 for Newton.SuNAlgebra.jacobi_identity_alt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:41:39.423254+00:00
-- url     : https://prove2.me/submissions/05362b30-859e-4de1-a9ae-04fc1470b4ac

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
    ⁅A, ⁅B, C⁆⁆ = ⁅⁅A, B⁆, C⁆ + ⁅B, ⁅A, C⁆⁆ :=
  leibniz_lie A B C
end SuNAlgebra
end Newton
