-- Prove2me | solution 1 for KendallBD.Sol.W_ode
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:47:24.867604+00:00
-- url     : https://prove2.me/submissions/cb64699c-67fe-475b-b41b-27e40ad1e1a7

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

set_option autoImplicit false
open Filter
open scoped Topology

open KendallBD.Sol in
theorem solution (lam mu : ℝ → ℝ) (hlam : Continuous lam)
    (hmu : Continuous mu) :
    W lam mu 0 = 1 ∧
      ∀ t : ℝ, HasDerivAt (W lam mu)
        (mu t - (mu t - lam t) * W lam mu t) t := by
  have hc : Continuous (fun τ => mu τ - lam τ) := hmu.sub hlam
  have hrho : ∀ t, HasDerivAt (rho lam mu) (mu t - lam t) t := fun t =>
    (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hrc : Continuous (rho lam mu) := continuous_iff_continuousAt.2 fun t => (hrho t).continuousAt
  constructor
  · simp [W, rho]
  · intro t
    have h1 : HasDerivAt (fun s => Real.exp (-rho lam mu s))
        (Real.exp (-rho lam mu t) * (-(mu t - lam t))) t :=
      ((hrho t).neg).exp
    have hg : Continuous (fun τ => Real.exp (rho lam mu τ) * mu τ) :=
      (Real.continuous_exp.comp hrc).mul hmu
    have h2 : HasDerivAt (fun s => 1 + ∫ τ in (0:ℝ)..s, Real.exp (rho lam mu τ) * mu τ)
        (Real.exp (rho lam mu t) * mu t) t :=
      ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add 1
    have h3 := h1.mul h2
    have e : Real.exp (-rho lam mu t) * Real.exp (rho lam mu t) = 1 := by
      rw [← Real.exp_add]; simp
    have hW : W lam mu t = Real.exp (-rho lam mu t) *
        (1 + ∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * mu τ) := rfl
    refine (h3 : HasDerivAt (W lam mu) _ t).congr_deriv ?_
    rw [hW]
    linear_combination (mu t) * e
