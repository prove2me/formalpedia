-- Prove2me | solution 1 for Newton.Complex.re_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:16:03.161322+00:00
-- url     : https://prove2.me/submissions/cdb8efe9-0c5e-40ad-8bea-f5cf01c4bff9

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
namespace Complex
theorem _root_.solution {α : Type*} (s : Finset α) (f : α → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s hnotin ih => simp [Finset.sum_insert hnotin, ih]
end Complex
end Newton
