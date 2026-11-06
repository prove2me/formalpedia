-- Prove2me | solution 2 for OAI.SevenEighths.CubicSieve.energy_le_squaredNorm
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:34.233652+00:00
-- url     : https://prove2.me/submissions/da153b32-07f7-4eb7-af9f-55ddd69b94a8

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

theorem solution (A : Matrix m n ℂ) (c : n → ℂ) :
    (∑ i, ‖∑ j, A i j * c j‖ ^ 2) ≤ squaredNorm A * ∑ j, ‖c j‖ ^ 2 := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 c
  have h1 : ‖operator A x‖ ≤ ‖operator A‖ * ‖x‖ := (operator A).le_opNorm x
  have h2 : ∀ i, (operator A x) i = ∑ j, A i j * c j := by
    intro i
    simp [operator, x, Matrix.mulVec, dotProduct]
  have h3 : ‖operator A x‖ ^ 2 = ∑ i, ‖∑ j, A i j * c j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [h2]
  have h4 : ‖x‖ ^ 2 = ∑ j, ‖c j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  rw [← h3, ← h4]
  calc ‖operator A x‖ ^ 2 ≤ (‖operator A‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = squaredNorm A * ‖x‖ ^ 2 := by rw [mul_pow]; rfl
