-- Prove2me | solution 1 for MathematicsOfWater.averageVelocity_poiseuilleProfile
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T04:09:04.376775+00:00
-- url     : https://prove2.me/submissions/1abdbef9-9d7d-4df7-97ef-6499883db67c

import Mathlib
import Definitions.Def_MathematicsOfWater_PipeFlow

set_option autoImplicit false

open Real MathematicsOfWater in
theorem water_flowRate_poiseuille_aux (η L Δp d : ℝ) :
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

open Real MathematicsOfWater in
theorem solution (η L Δp d : ℝ)
    (hη : 0 < η) (hL : 0 < L) (hd : 0 < d) :
    averageVelocity d (poiseuilleProfile η L Δp d) = Δp * d ^ 2 / (32 * η * L) := by
  unfold averageVelocity
  rw [water_flowRate_poiseuille_aux]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hd' : d ≠ 0 := hd.ne'
  have hη' : η ≠ 0 := hη.ne'
  have hL' : L ≠ 0 := hL.ne'
  field_simp
  ring
