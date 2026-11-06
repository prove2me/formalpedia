-- Prove2me | solution 2 for OAI.SevenEighths.CubicSieve.cubic_square_eq_star
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:26.793917+00:00
-- url     : https://prove2.me/submissions/66cc3c40-7fdc-476e-8a1b-85d4ae569d16

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Algebra
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite Rˣ]
theorem OA1Aux.cubic_inv_eq_square {R : Type*} [CommRing R] (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) :
    χ⁻¹ = χ ^ 2 := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact hχ

theorem solution (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 2 = star (χ x) := by
  rw [MulChar.star_apply', OA1Aux.cubic_inv_eq_square χ hχ, MulChar.pow_apply' χ (by norm_num)]
