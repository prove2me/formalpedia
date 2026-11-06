-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.squaredNorm_transpose
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:59:27.312338+00:00
-- url     : https://prove2.me/submissions/7c87f697-e435-4f3b-b1bb-ee448668ee7b

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem norm_conjugateVector_aux (x : EuclideanSpace ℂ n) :
    ‖conjugateVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, conjugateVector, norm_star]

private theorem operator_conjugate_apply_aux (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    operator (fun i j => star (A i j)) x = conjugateVector (operator A (conjugateVector x)) := by
  ext i
  change (∑ j, star (A i j) * x j) = star (∑ j, A i j * star (x j))
  simp only [star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

private theorem operator_conjugate_norm_le_aux (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [operator_conjugate_apply_aux, norm_conjugateVector_aux]
  simpa only [norm_conjugateVector_aux] using (operator A).le_opNorm (conjugateVector x)

private theorem operator_conjugate_norm_aux (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ = ‖operator A‖ := by
  apply le_antisymm (operator_conjugate_norm_le_aux A)
  simpa only [star_star] using operator_conjugate_norm_le_aux (fun i j => star (A i j))

private theorem operator_conjTranspose_norm_aux (A : Matrix m n ℂ) :
    ‖operator A.conjTranspose‖ = ‖operator A‖ := by
  have heq : operator A.conjTranspose = (operator A).adjoint := by
    unfold operator
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  rw [heq]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem solution (A : Matrix m n ℂ) :
    squaredNorm A.transpose = squaredNorm A := by
  unfold squaredNorm
  have h := operator_conjugate_norm_aux A.transpose
  change ‖operator A.conjTranspose‖ = ‖operator A.transpose‖ at h
  rw [operator_conjTranspose_norm_aux] at h
  exact congrArg (fun x : ℝ => x ^ 2) h.symm
