-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.operator_conjTranspose_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:20.082991+00:00
-- url     : https://prove2.me/submissions/eb1a6fc9-ed08-4ff9-87fb-c9ebde96d281

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (A : Matrix m n ℂ) :
    ‖operator A.conjTranspose‖ = ‖operator A‖ := by
  have heq : operator A.conjTranspose = (operator A).adjoint := by
    unfold operator
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  rw [heq]
  exact ContinuousLinearMap.adjoint.norm_map _
end OAI.SevenEighths.CubicSieve
