-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.cubic_cube_eq_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:00.965032+00:00
-- url     : https://prove2.me/submissions/a1b369c5-d7eb-4e1c-bdd1-c53c20e2eb3c

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
    χ (x ^ 3) = if IsUnit x then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ]
  by_cases hx : IsUnit x
  · rw [if_pos hx, MulChar.one_apply hx]
  · rw [if_neg hx, MulChar.map_nonunit _ hx]
end OAI.SevenEighths.CubicSieve
