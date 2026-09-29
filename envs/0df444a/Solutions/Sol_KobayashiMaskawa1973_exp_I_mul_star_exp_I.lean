-- Prove2me | solution 1 for KobayashiMaskawa1973.exp_I_mul_star_exp_I
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:46:09.416367+00:00
-- url     : https://prove2.me/submissions/92a36a97-91d9-4d70-9aa9-47722f1bd7dc

import Mathlib

open Complex ComplexConjugate

theorem solution (t : ℝ) :
    exp ((t : ℂ) * I) * star (exp ((t : ℂ) * I)) = 1 := by
  rw [star_def, ← exp_conj, ← exp_add]
  rw [show (t : ℂ) * I + conj ((t : ℂ) * I) = 0 by simp [map_mul, conj_ofReal, conj_I]]
  exact exp_zero
