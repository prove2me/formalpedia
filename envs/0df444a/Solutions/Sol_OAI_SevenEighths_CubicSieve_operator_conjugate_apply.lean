-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.operator_conjugate_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:12.858371+00:00
-- url     : https://prove2.me/submissions/994bc2b4-c416-4752-b9cb-39109f8f927b

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
import Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_apply
import Theorems.Thm_OAI_SevenEighths_CubicSieve_conjugateVector_apply
import Theorems.Thm_OAI_SevenEighths_CubicSieve_norm_conjugateVector
attribute [local simp] OAI.SevenEighths.CubicSieve.operator_apply
attribute [local simp] OAI.SevenEighths.CubicSieve.conjugateVector_apply
attribute [local simp] OAI.SevenEighths.CubicSieve.norm_conjugateVector

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq m]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    operator (fun i j => star (A i j)) x = conjugateVector (operator A (conjugateVector x)) := by
  ext i
  change (∑ j, star (A i j) * x j) = star (∑ j, A i j * star (x j))
  simp only [star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _
end OAI.SevenEighths.CubicSieve
