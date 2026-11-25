-- Prove2me | solution 1 for Newton.SuNAlgebra.lie_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:30:46.89219+00:00
-- url     : https://prove2.me/submissions/b1e0d030-04b7-455c-9791-6ff5731da675

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
    (⁅A, B⁆ : SuNAlgebra N).matrix = ⁅A.matrix, B.matrix⁆ := rfl
end SuNAlgebra
end Newton
