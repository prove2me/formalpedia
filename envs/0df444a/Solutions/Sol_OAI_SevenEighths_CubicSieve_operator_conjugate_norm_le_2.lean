-- Prove2me | solution 2 for OAI.SevenEighths.CubicSieve.operator_conjugate_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:36.069808+00:00
-- url     : https://prove2.me/submissions/b5be079a-6683-47ac-8cc1-2eb42e5e2c4b

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq m]
theorem OA1Aux.operator_conjTranspose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℂ) :
    operator A.conjTranspose = ContinuousLinearMap.adjoint (operator A) := by
  apply ContinuousLinearMap.coe_injective
  exact Matrix.toEuclideanLin_conjTranspose_eq_adjoint A

theorem OA1Aux.norm_conjugateVector {n : Type*} [Fintype n] (x : EuclideanSpace ℂ n) :
    ‖conjugateVector x‖ = ‖x‖ := by
  simp [EuclideanSpace.norm_eq, conjugateVector]

theorem OA1Aux.operator_conj_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    operator (fun i j => star (A i j)) x = conjugateVector (operator A (conjugateVector x)) := by
  ext i
  change (Matrix.mulVec (fun i j => star (A i j)) x.ofLp) i =
    star ((Matrix.mulVec A (conjugateVector x).ofLp) i)
  simp [conjugateVector, Matrix.mulVec, dotProduct, star_sum, mul_comm]

theorem OA1Aux.operator_conj_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ‖operator (fun i j => star (A i j))‖ ≤ ‖operator A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  rw [OA1Aux.operator_conj_apply, OA1Aux.norm_conjugateVector]
  calc ‖operator A (conjugateVector x)‖ ≤ ‖operator A‖ * ‖conjugateVector x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖operator A‖ * ‖x‖ := by rw [OA1Aux.norm_conjugateVector]

theorem OA1Aux.operator_conj_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ‖operator (fun i j => star (A i j))‖ = ‖operator A‖ := by
  refine le_antisymm (OA1Aux.operator_conj_le A) ?_
  have := OA1Aux.operator_conj_le (fun i j => star (A i j))
  simpa only [star_star] using this

theorem OA1Aux.operator_conjTranspose_norm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℂ) : ‖operator A.conjTranspose‖ = ‖operator A‖ := by
  rw [OA1Aux.operator_conjTranspose]
  exact LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (operator A)

theorem solution (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ ≤ ‖operator A‖ := by
  exact OA1Aux.operator_conj_le A
