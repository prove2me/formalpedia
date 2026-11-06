-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.cubic_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:58:58.010989+00:00
-- url     : https://prove2.me/submissions/d0677c7f-1e26-4e40-bc06-5b36da74c3d2

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

variable {R : Type*} [CommRing R]

theorem solution (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    ‖χ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · have hpow : χ x ^ 3 = 1 := by
      calc
        χ x ^ 3 = (χ ^ 3) x := (χ.pow_apply' (by norm_num) x).symm
        _ = (1 : MulChar R ℂ) x := congrArg (fun ψ : MulChar R ℂ ↦ ψ x) hχ
        _ = 1 := MulChar.one_apply hx
    exact (Complex.norm_eq_one_of_pow_eq_one hpow (by norm_num)).le
  · rw [χ.map_nonunit hx, norm_zero]
    exact zero_le_one
