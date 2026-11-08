-- Prove2me | solution 1 for LoockCVQEC.RepCode.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:38:24.605177+00:00
-- url     : https://prove2.me/submissions/2fc982d7-5686-46e7-9dec-34b63007f9d9

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

open Real

open LoockCVQEC.RepCode in
theorem solution (xb pb r : ℝ) (x p : Fin 3 → ℝ) :
    encode (prodW xb pb r) x p =
      (2 / π) ^ 3 * exp (-2 * (1 / √3 * (x 0 + x 1 + x 2) - xb) ^ 2
        - 2 / 3 * exp (-2 * r) * ((p 0 - p 1) ^ 2 + (p 1 - p 2) ^ 2 + (p 0 - p 2) ^ 2)
        - 2 * (1 / √3 * (p 0 + p 1 + p 2) - pb) ^ 2
        - 2 / 3 * exp (2 * r) * ((x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + (x 0 - x 2) ^ 2)) := by
  have T0 : ∀ v : Fin 3 → ℝ, (Matrix.mulVec tritter v) 0 = 1 / √3 * (v 0 + v 1 + v 2) := by
    intro v; simp [tritter, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have T1 : ∀ v : Fin 3 → ℝ, (Matrix.mulVec tritter v) 1 = √(2 / 3) * v 0 - 1 / √6 * v 1 - 1 / √6 * v 2 := by
    intro v; simp [tritter, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have T2 : ∀ v : Fin 3 → ℝ, (Matrix.mulVec tritter v) 2 = 1 / √2 * v 1 - 1 / √2 * v 2 := by
    intro v; simp [tritter, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have h6 : (0 : ℝ) < √6 := Real.sqrt_pos.mpr (by norm_num)
  have h23 : √(2 / 3) = 2 * (1 / √6) := by
    rw [mul_one_div, eq_div_iff h6.ne', ← Real.sqrt_mul (by norm_num),
      show (2 / 3 : ℝ) * 6 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hu : (1 / √6) ^ 2 = 1 / 6 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  have hw : (1 / √2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hq : ∀ v : Fin 3 → ℝ,
      (2 * (1 / √6) * v 0 - 1 / √6 * v 1 - 1 / √6 * v 2) ^ 2 + (1 / √2 * v 1 - 1 / √2 * v 2) ^ 2
        = ((v 0 - v 1) ^ 2 + (v 1 - v 2) ^ 2 + (v 0 - v 2) ^ 2) / 3 := by
    intro v
    linear_combination (2 * v 0 - v 1 - v 2) ^ 2 * hu + (v 1 - v 2) ^ 2 * hw
  have key : ∀ A B C : ℝ, 2 / π * exp A * (2 / π * exp B) * (2 / π * exp C) =
      (2 / π) ^ 3 * exp (A + B + C) := by
    intro A B C; rw [exp_add, exp_add]; ring
  unfold encode prodW inW ancW
  rw [T0, T0, T1, T1, T2, T2, h23, key]
  congr 2
  linear_combination (-2 * exp (2 * r)) * hq x + (-2 * exp (-2 * r)) * hq p
