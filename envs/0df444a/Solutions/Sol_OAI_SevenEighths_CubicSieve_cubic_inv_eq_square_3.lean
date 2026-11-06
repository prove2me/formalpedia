-- Prove2me | solution 3 for OAI.SevenEighths.CubicSieve.cubic_inv_eq_square
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:18.970558+00:00
-- url     : https://prove2.me/submissions/cff46abc-24a0-4ac6-92c8-7b525868a022

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
omit [Finite Rˣ]
theorem solution (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) :
    χ⁻¹ = χ ^ 2 := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact hχ
