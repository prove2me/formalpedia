-- Prove2me | solution 2 for OAI.SevenEighths.InverseMoment.inverse_cube_square_eq_sixth
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:30.019344+00:00
-- url     : https://prove2.me/submissions/2700d2d6-a94c-40f2-a55a-9e8ef1a4f899

import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Overlap
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open UniqueFactorizationMonoid
theorem solution {z : ℂ} (h : z ^ 6 = 0 ∨ z ^ 6 = 1) :
    ((z ^ 3)⁻¹) ^ 2 = z ^ 6 := by
  rcases h with h | h
  · have : z = 0 := (pow_eq_zero_iff (by norm_num)).mp h
    subst this
    norm_num
  · rw [inv_pow, ← pow_mul, show 3 * 2 = 6 from rfl, h]
    simp
