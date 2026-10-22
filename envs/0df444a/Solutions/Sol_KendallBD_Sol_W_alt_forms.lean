-- Prove2me | solution 1 for KendallBD.Sol.W_alt_forms
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:51:39.634924+00:00
-- url     : https://prove2.me/submissions/6be5cab9-22b0-4ade-9930-807140a44f24

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

set_option autoImplicit false
open Filter
open scoped Topology

open KendallBD.Sol in
theorem solution (lam mu : ℝ → ℝ) (hlam : Continuous lam)
    (hmu : Continuous mu) :
    ∀ t : ℝ, 0 ≤ t →
      W lam mu t = 1 + Real.exp (-rho lam mu t) *
        (∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * lam τ) ∧
      W lam mu t = (1 + Real.exp (-rho lam mu t)) / 2 +
        Real.exp (-rho lam mu t) / 2 *
        (∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * (lam τ + mu τ)) := by
  intro t _
  have hc : Continuous (fun τ => mu τ - lam τ) := hmu.sub hlam
  have hrho : ∀ s, HasDerivAt (rho lam mu) (mu s - lam s) s := fun s =>
    (hc.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hrc : Continuous (rho lam mu) := continuous_iff_continuousAt.2 fun s => (hrho s).continuousAt
  have hEc : Continuous (fun τ => Real.exp (rho lam mu τ)) := Real.continuous_exp.comp hrc
  have hd : ∀ s ∈ Set.uIcc (0:ℝ) t, HasDerivAt (fun τ => Real.exp (rho lam mu τ))
      (Real.exp (rho lam mu s) * (mu s - lam s)) s := fun s _ => (hrho s).exp
  have hint : IntervalIntegrable (fun s => Real.exp (rho lam mu s) * (mu s - lam s))
      MeasureTheory.volume 0 t := (hEc.mul hc).intervalIntegrable _ _
  have h0 := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  have hρ0 : rho lam mu 0 = 0 := by simp [rho]
  simp only [hρ0, Real.exp_zero] at h0
  have hiM : IntervalIntegrable (fun s => Real.exp (rho lam mu s) * mu s)
      MeasureTheory.volume 0 t := (hEc.mul hmu).intervalIntegrable _ _
  have hiL : IntervalIntegrable (fun s => Real.exp (rho lam mu s) * lam s)
      MeasureTheory.volume 0 t := (hEc.mul hlam).intervalIntegrable _ _
  have hsub : (∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * (mu τ - lam τ)) =
      (∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * mu τ) -
      ∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * lam τ := by
    rw [← intervalIntegral.integral_sub hiM hiL]
    congr 1; ext τ; ring
  have hI : (∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * mu τ) =
      Real.exp (rho lam mu t) - 1 + ∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * lam τ := by
    linarith
  have hsum : (∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * (lam τ + mu τ)) =
      (∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * lam τ) +
      ∫ τ in (0:ℝ)..t, Real.exp (rho lam mu τ) * mu τ := by
    rw [← intervalIntegral.integral_add hiL hiM]
    congr 1; ext τ; ring
  have e : Real.exp (-rho lam mu t) * Real.exp (rho lam mu t) = 1 := by
    rw [← Real.exp_add]; simp
  have hW : W lam mu t = Real.exp (-rho lam mu t) *
      (1 + ∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * mu τ) := rfl
  rw [hsum, hW]
  constructor
  · rw [hI]; linear_combination e
  · linear_combination (Real.exp (-rho lam mu t) / 2) * hI + (1 / 2) * e
