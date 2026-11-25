-- Prove2me | solution 1 for Newton.SuNAlgebra.ext_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:10:30.695467+00:00
-- url     : https://prove2.me/submissions/fc00fcba-fa90-426d-83d2-60c5abfd1e64

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
open Newton.SuNAlgebra
namespace Newton.SuNAlgebra
theorem _root_.solution {A : SuNAlgebra N} (h : A.matrix = 0) : A = 0 :=
  ext h
end Newton.SuNAlgebra
