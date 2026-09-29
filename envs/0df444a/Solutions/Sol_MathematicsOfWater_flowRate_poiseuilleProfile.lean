-- Prove2me | solution 1 for MathematicsOfWater.flowRate_poiseuilleProfile
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T04:09:04.394573+00:00
-- url     : https://prove2.me/submissions/7a12e41a-abd0-4561-b206-44de9d3ad419

import Mathlib
import Definitions.Def_MathematicsOfWater_PipeFlow

set_option autoImplicit false

open Real MathematicsOfWater in
theorem solution (η L Δp d : ℝ)
    (hη : 0 < η) (hL : 0 < L) (hd : 0 < d) :
    flowRate d (poiseuilleProfile η L Δp d) = π * Δp * d ^ 4 / (128 * η * L) := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun r : ℝ => Δp / (4 * η * L) * (2 * π) * (d ^ 2 / 4 * (r ^ 2 / 2) - r ^ 4 / 4))
      (poiseuilleProfile η L Δp d x * (2 * π * x)) x := by
    intro x
    have h := ((((hasDerivAt_pow 2 x).div_const 2).const_mul (d ^ 2 / 4)).sub
      ((hasDerivAt_pow 4 x).div_const 4)).const_mul (Δp / (4 * η * L) * (2 * π))
    refine h.congr_deriv ?_
    unfold poiseuilleProfile
    push_cast
    ring
  unfold flowRate
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (by unfold poiseuilleProfile; apply Continuous.intervalIntegrable; fun_prop)]
  field_simp
  ring
