-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.cubic_fourth_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:24.328736+00:00
-- url     : https://prove2.me/submissions/07264151-0149-4b24-832b-3d2ce20d5de7

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
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 4 = χ x := by
  have h : χ ^ 4 = χ := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hχ, one_mul, pow_one]
  rw [← MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), h]
end OAI.SevenEighths.CubicSieve
