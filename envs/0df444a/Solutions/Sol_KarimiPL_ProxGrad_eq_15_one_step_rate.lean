-- Prove2me | solution 1 for KarimiPL.ProxGrad.eq_15_one_step_rate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:12:19.208858+00:00
-- url     : https://prove2.me/submissions/4b1802fb-5f84-42eb-b003-3e4da842b3a4

import Mathlib
import Definitions.Def_KarimiPL_ProxGrad_IsProxGradStep
import Definitions.Def_KarimiPL_ProxGrad_Dg
import Definitions.Def_KarimiPL_ProxGrad_IsProxPL
import Definitions.Def_KarimiPL_ProxGrad_IsProxGradRun

open scoped InnerProductSpace

namespace Aux_KPL15

theorem iInf_eq_of_min {α : Type*} {D : Set α} (F : D → ℝ) (z : D) (h : ∀ y, F z ≤ F y) :
    ⨅ y, F y = F z := by
  haveI : Nonempty D := ⟨z⟩
  have hbdd : BddBelow (Set.range F) := ⟨F z, by rintro _ ⟨y, rfl⟩; exact h y⟩
  exact le_antisymm (ciInf_le hbdd z) (le_ciInf h)

end Aux_KPL15

open KarimiPL.ProxGrad in
theorem solution {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} {L μ : ℝ} (hL : 0 < L) (hf : Differentiable ℝ f)
    (hsmooth : ∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (hg : ConvexOn ℝ D g)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxD : xstar ∈ D)
    (hmin : ∀ z ∈ D, f xstar + g xstar ≤ f z + g z)
    (hPL : IsProxPL f g D L μ xstar)
    {x : ℕ → EuclideanSpace ℝ (Fin d)} (hx0 : x 0 ∈ D)
    (hrun : IsProxGradRun f g D L x)
    (k : ℕ) :
    f (x (k + 1)) + g (x (k + 1)) - (f xstar + g xstar) ≤
      (1 - μ / L) * (f (x k) + g (x k) - (f xstar + g xstar)) := by
  have hxk : ∀ k, x k ∈ D := by
    intro k
    cases k with
    | zero => exact hx0
    | succ k => exact (hrun k).1
  obtain ⟨hpD, hstep⟩ := hrun k
  have hinf : (⨅ y : D, (⟪gradient f (x k), (y : EuclideanSpace ℝ (Fin d)) - x k⟫_ℝ +
      L / 2 * ‖(y : EuclideanSpace ℝ (Fin d)) - x k‖ ^ 2 + g y - g (x k))) =
      ⟪gradient f (x k), x (k + 1) - x k⟫_ℝ + L / 2 * ‖x (k + 1) - x k‖ ^ 2 +
        g (x (k + 1)) - g (x k) :=
    Aux_KPL15.iInf_eq_of_min _ ⟨x (k + 1), hpD⟩ (fun y => hstep y y.2)
  have hPL' := hPL.2 (x k) (hxk k) ⟨x (k + 1), hrun k⟩
  unfold Dg at hPL'
  rw [hinf] at hPL'
  have hs := hsmooth (x k) (x (k + 1))
  have key2 : L * (⟪gradient f (x k), x (k + 1) - x k⟫_ℝ + L / 2 * ‖x (k + 1) - x k‖ ^ 2 +
      g (x (k + 1)) - g (x k)) ≤ -(μ * (f (x k) + g (x k) - (f xstar + g xstar))) := by
    linarith
  have hBp : ⟪gradient f (x k), x (k + 1) - x k⟫_ℝ + L / 2 * ‖x (k + 1) - x k‖ ^ 2 +
      g (x (k + 1)) - g (x k) ≤ -(μ * (f (x k) + g (x k) - (f xstar + g xstar))) / L := by
    rw [le_div_iff₀ hL]
    linarith
  have e : (1 - μ / L) * (f (x k) + g (x k) - (f xstar + g xstar)) =
      (f (x k) + g (x k) - (f xstar + g xstar)) +
        -(μ * (f (x k) + g (x k) - (f xstar + g xstar))) / L := by
    ring
  rw [e]
  linarith
