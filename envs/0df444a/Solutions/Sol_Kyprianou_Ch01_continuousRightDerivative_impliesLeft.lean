-- Prove2me | solution 1 for Kyprianou.Ch01.continuousRightDerivative_impliesLeft
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T17:51:47.573252+00:00
-- url     : https://prove2.me/submissions/7ddbbf28-5ba4-47b7-b1e0-f0d65dd0bf3d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false

/-- A continuous right derivative with continuous values determines the left derivative. -/
theorem solution
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hg : Continuous g)
    (hright : ∀ x : ℝ, 0 ≤ x →
      HasDerivWithinAt f (g x) (Ioi x) x)
    (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt f (g t) (Iic t) t := by
  let F : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..u, g x
  have hF (u : ℝ) (hu : u ∈ Icc (0 : ℝ) t) :
      F u = f u - f 0 := by
    have hfcont : ContinuousOn f (Icc (0 : ℝ) u) :=
      hf.mono (fun x hx => hx.1)
    have hd : ∀ x ∈ Ioo (0 : ℝ) u,
        HasDerivWithinAt f (g x) (Ioi x) x := by
      intro x hx
      exact hright x hx.1.le
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le_real
      hu.1 hfcont hd hg.integrableOn_Icc
  have hFderiv : HasDerivAt F (g t) t := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable (0 : ℝ) t)
      (hg.stronglyMeasurableAtFilter volume (𝓝 t)) hg.continuousAt
  have hD : HasDerivWithinAt (fun u => F u + f 0) (g t) (Iic t) t :=
    (hFderiv.add_const (f 0)).hasDerivWithinAt
  have hEvt : f =ᶠ[𝓝[≤] t] (fun u => F u + f 0) := by
    filter_upwards [Icc_mem_nhdsLE ht] with u hu
    have h := hF u hu
    linarith
  apply hD.congr_of_eventuallyEq hEvt
  have h := hF t ⟨ht.le, le_rfl⟩
  linarith
