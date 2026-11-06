-- Prove2me | solution 2 for OAI.SevenEighths.CubicSieve.cubic_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:01.811792+00:00
-- url     : https://prove2.me/submissions/0b30caa4-8e78-4f29-898c-c65f9a323fbf

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
    ‖χ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · have hc : χ x ^ 3 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ, MulChar.one_apply hx]
    exact (Complex.norm_eq_one_of_pow_eq_one hc (by decide)).le
  · rw [MulChar.map_nonunit _ hx, norm_zero]
    exact zero_le_one
end OAI.SevenEighths.CubicSieve
