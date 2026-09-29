-- Prove2me | solution 1 for NewtonGravitation.norm_pointForce
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:19:49.064262+00:00
-- url     : https://prove2.me/submissions/5502c0f6-d21a-41c7-a016-f76f4c68d964

import Definitions.Def_NewtonGravitation_Defs

theorem solution (m₁ m₂ : ℝ) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (r₁ r₂ : NewtonGravitation.Space) (hr : r₁ ≠ r₂) :
    ‖NewtonGravitation.pointForce m₁ m₂ r₁ r₂‖ =
      NewtonGravitation.G * m₁ * m₂ / ‖r₂ - r₁‖ ^ 2 := by
  have hd : ‖r₂ - r₁‖ ≠ 0 := by
    intro h
    have : r₂ - r₁ = 0 := norm_eq_zero.mp h
    exact hr (eq_of_sub_eq_zero this).symm
  have hg : 0 ≤ NewtonGravitation.G := by norm_num [NewtonGravitation.G]
  have hc : 0 ≤ NewtonGravitation.G * m₁ * m₂ / ‖r₂ - r₁‖ ^ 2 := by
    exact div_nonneg (mul_nonneg (mul_nonneg hg hm₁) hm₂) (sq_nonneg _)
  unfold NewtonGravitation.pointForce
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [abs_neg, abs_of_nonneg hc, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  rw [inv_mul_cancel₀ hd, mul_one]

#print axioms solution
