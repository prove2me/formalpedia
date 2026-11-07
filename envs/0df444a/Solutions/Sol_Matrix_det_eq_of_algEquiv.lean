-- Prove2me | solution 1 for Matrix.det_eq_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:46.09413+00:00
-- url     : https://prove2.me/submissions/37dd01c5-12dc-45f6-a9e8-83cf209ab406

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm

set_option autoImplicit false
open scoped Matrix
open Matrix
open scoped Polynomial
namespace Matrix
theorem _root_.solution
    {K A n : Type*} [Field K] [Ring A] [Algebra K A]
    [Fintype n] [DecidableEq n]
    (e₁ e₂ : A ≃ₐ[K] Matrix n n K) (x : A) :
    Matrix.det (e₁ x) = Matrix.det (e₂ x) := by
  simpa using (Matrix.det_map (e₁.symm.trans e₂) (e₁ x)).symm
end Matrix
