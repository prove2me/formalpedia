-- Prove2me | solution 1 for KarimiPL.ProxGrad.theorem_5_prox_grad_linear_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T14:44:03.620201+00:00
-- url     : https://prove2.me/submissions/4baae4c9-ee7f-4c5e-a2ad-70ee7f33e1c1

import Mathlib
import Definitions.Def_KarimiPL_ProxGrad_IsProxGradStep
import Definitions.Def_KarimiPL_ProxGrad_Dg
import Definitions.Def_KarimiPL_ProxGrad_IsProxPL
import Definitions.Def_KarimiPL_ProxGrad_IsProxGradRun

set_option autoImplicit false

open scoped InnerProductSpace

namespace KarimiPLProxGradSol

open KarimiPL.ProxGrad

theorem dg_eq_of_step {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} {α : ℝ} {x p : EuclideanSpace ℝ (Fin d)}
    (h : IsProxGradStep f g D α x p) :
    Dg f g D α x = -2 * α * (⟪gradient f x, p - x⟫_ℝ + α / 2 * ‖p - x‖ ^ 2 + g p - g x) := by
  unfold Dg
  congr 1
  apply le_antisymm
  · have hb : BddBelow (Set.range (fun y : D =>
        ⟪gradient f x, (y : EuclideanSpace ℝ (Fin d)) - x⟫_ℝ +
          α / 2 * ‖(y : EuclideanSpace ℝ (Fin d)) - x‖ ^ 2 + g y - g x)) := by
      refine ⟨⟪gradient f x, p - x⟫_ℝ + α / 2 * ‖p - x‖ ^ 2 + g p - g x, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact h.2 y y.2
    exact ciInf_le hb (⟨p, h.1⟩ : D)
  · haveI : Nonempty D := ⟨⟨p, h.1⟩⟩
    exact le_ciInf (fun y => h.2 y y.2)

theorem alg (L μ G Gp φ : ℝ) (hL : 0 < L) (h1 : μ * G ≤ 1 / 2 * (-2 * L * φ))
    (h2 : Gp ≤ G + φ) : Gp ≤ (1 - μ / L) * G := by
  have h3 : μ * G ≤ -φ * L := by linarith
  have h4 : μ / L * G ≤ -φ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    exact h3
  have h5 : (1 - μ / L) * G = G - μ / L * G := by ring
  linarith

theorem one_step {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} {L μ : ℝ} (hL : 0 < L)
    (hsmooth : ∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    {xstar : EuclideanSpace ℝ (Fin d)} (hPL : IsProxPL f g D L μ xstar)
    {x p : EuclideanSpace ℝ (Fin d)} (hxD : x ∈ D) (h : IsProxGradStep f g D L x p) :
    f p + g p - (f xstar + g xstar) ≤ (1 - μ / L) * (f x + g x - (f xstar + g xstar)) := by
  have hpl := hPL.2 x hxD ⟨p, h⟩
  rw [dg_eq_of_step h] at hpl
  have hs := hsmooth x p
  apply alg L μ _ _ (⟪gradient f x, p - x⟫_ℝ + L / 2 * ‖p - x‖ ^ 2 + g p - g x) hL hpl
  linarith

theorem seq_rate (G : ℕ → ℝ) (c : ℝ) (hnn : ∀ k, 0 ≤ G k)
    (hstep : ∀ k, G (k + 1) ≤ c * G k) : ∀ k, G k ≤ c ^ k * G 0 := by
  intro k
  rcases le_or_gt 0 c with hc | hc
  · induction k with
    | zero => simp
    | succ n ih =>
      calc G (n + 1) ≤ c * G n := hstep n
        _ ≤ c * (c ^ n * G 0) := mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (n + 1) * G 0 := by ring
  · have h1 := hstep 0
    have h2 := hnn 1
    have h3 := hnn 0
    have h0 : G 0 = 0 := by
      apply le_antisymm _ h3
      nlinarith
    have hall : ∀ k, G k ≤ 0 := by
      intro k
      cases k with
      | zero => exact h0.le
      | succ n =>
        have := hstep n
        have := hnn n
        nlinarith
    rw [h0, mul_zero]
    exact hall k

end KarimiPLProxGradSol

open KarimiPL.ProxGrad InnerProductSpace in
theorem solution {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} {L μ : ℝ} (hL : 0 < L) (hf : Differentiable ℝ f)
    (hsmooth : ∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (hg : ConvexOn ℝ D g)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxD : xstar ∈ D)
    (hmin : ∀ z ∈ D, f xstar + g xstar ≤ f z + g z)
    (hPL : IsProxPL f g D L μ xstar)
    {x : ℕ → EuclideanSpace ℝ (Fin d)} (hx0 : x 0 ∈ D)
    (hrun : IsProxGradRun f g D L x) :
    ∀ k : ℕ, f (x k) + g (x k) - (f xstar + g xstar) ≤
      (1 - μ / L) ^ k * (f (x 0) + g (x 0) - (f xstar + g xstar)) := by
  have hmem : ∀ k, x k ∈ D := by
    intro k
    cases k with
    | zero => exact hx0
    | succ k => exact (hrun k).1
  have hnn : ∀ k, 0 ≤ f (x k) + g (x k) - (f xstar + g xstar) := by
    intro k
    have := hmin _ (hmem k)
    linarith
  have hstep : ∀ k, f (x (k + 1)) + g (x (k + 1)) - (f xstar + g xstar) ≤
      (1 - μ / L) * (f (x k) + g (x k) - (f xstar + g xstar)) := fun k =>
    KarimiPLProxGradSol.one_step hL hsmooth hPL (hmem k) (hrun k)
  exact KarimiPLProxGradSol.seq_rate
    (fun k => f (x k) + g (x k) - (f xstar + g xstar)) (1 - μ / L) hnn hstep
