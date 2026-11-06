-- Prove2me | solution 1 for OAI.ShortDraftLocal.sextic_character_exponent
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:57:53.165749+00:00
-- url     : https://prove2.me/submissions/e17b9b0a-9cd2-465d-9acf-69882c7cb809

import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.Tactic.Group

set_option autoImplicit false

open MulChar

variable {F : Type*} [Field F]

theorem solution (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1) :
    χ⁻¹ * χ⁻¹ ^ 2 = χ ^ 3 := by
  calc
    χ⁻¹ * χ⁻¹ ^ 2 = (χ ^ 3)⁻¹ := by group
    _ = χ ^ 3 := inv_eq_of_mul_eq_one_left (by
      rw [← pow_add]
      norm_num
      exact hχ)
