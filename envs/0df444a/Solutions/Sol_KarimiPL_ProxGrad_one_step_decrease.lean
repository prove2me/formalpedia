-- Prove2me | solution 1 for KarimiPL.ProxGrad.one_step_decrease
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:55:53.89321+00:00
-- url     : https://prove2.me/submissions/29480a83-5f6b-4510-84a5-8360b0e344e2

import Mathlib
import Definitions.Def_KarimiPL_ProxGrad_IsProxGradStep
import Definitions.Def_KarimiPL_ProxGrad_Dg

open scoped InnerProductSpace

open KarimiPL.ProxGrad in
theorem solution {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} {L : ℝ} (hL : 0 < L) (hf : Differentiable ℝ f)
    (hsmooth : ∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    {x p : EuclideanSpace ℝ (Fin d)} (hp : IsProxGradStep f g D L x p) :
    f p + g p ≤ f x + g x - 1 / (2 * L) * Dg f g D L x := by
  obtain ⟨hpD, hpmin⟩ := hp
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = ⟪gradient f x, p - x⟫_ℝ + L / 2 * ‖p - x‖ ^ 2 + g p - g x :=
    ⟨_, rfl⟩
  have hI : (⨅ y : D, (⟪gradient f x, (y : EuclideanSpace ℝ (Fin d)) - x⟫_ℝ +
      L / 2 * ‖(y : EuclideanSpace ℝ (Fin d)) - x‖ ^ 2 + g y - g x)) = Φ := by
    rw [hΦ]
    apply le_antisymm
    · refine ciInf_le ⟨⟪gradient f x, p - x⟫_ℝ + L / 2 * ‖p - x‖ ^ 2 + g p - g x, ?_⟩ (⟨p, hpD⟩ : D)
      rintro _ ⟨y, rfl⟩
      exact hpmin y y.2
    · haveI : Nonempty D := ⟨⟨p, hpD⟩⟩
      exact le_ciInf fun y => hpmin y y.2
  unfold Dg
  rw [hI]
  have h2L : (2 * L) ≠ 0 := (mul_pos two_pos hL).ne'
  have e : 1 / (2 * L) * (-2 * L * Φ) = -Φ := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff h2L]
    ring
  rw [e]
  have := hsmooth x p
  linarith
