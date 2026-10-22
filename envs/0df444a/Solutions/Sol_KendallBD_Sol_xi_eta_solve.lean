-- Prove2me | solution 1 for KendallBD.Sol.xi_eta_solve
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:55:56.847755+00:00
-- url     : https://prove2.me/submissions/1f60b226-fe31-4500-a466-c78755565cae

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

set_option autoImplicit false
open Filter
open scoped Topology
open KendallBD.Sol

lemma kb_hrho (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu) (s : ℝ) :
    HasDerivAt (rho lam mu) (mu s - lam s) s :=
  ((hmu.sub hlam).integral_hasStrictDerivAt 0 s).hasDerivAt

lemma kb_hrc (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu) :
    Continuous (rho lam mu) :=
  continuous_iff_continuousAt.2 fun s => (kb_hrho lam mu hlam hmu s).continuousAt

lemma kb_W_first (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu) (t : ℝ) :
    W lam mu t = 1 + Real.exp (-rho lam mu t) *
        (∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * lam τ) := by
  have hc : Continuous (fun τ => mu τ - lam τ) := hmu.sub hlam
  have hrc := kb_hrc lam mu hlam hmu
  have hEc : Continuous (fun τ => Real.exp (rho lam mu τ)) := Real.continuous_exp.comp hrc
  have hd : ∀ s ∈ Set.uIcc (0:ℝ) t, HasDerivAt (fun τ => Real.exp (rho lam mu τ))
      (Real.exp (rho lam mu s) * (mu s - lam s)) s := fun s _ => (kb_hrho lam mu hlam hmu s).exp
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
  have e : Real.exp (-rho lam mu t) * Real.exp (rho lam mu t) = 1 := by
    rw [← Real.exp_add]; simp
  have hW : W lam mu t = Real.exp (-rho lam mu t) *
      (1 + ∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * mu τ) := rfl
  rw [hW, hI]; linear_combination e

lemma kb_W_ge_one (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu)
    (hlam0 : ∀ t, 0 ≤ t → 0 ≤ lam t) (t : ℝ) (ht : 0 ≤ t) : 1 ≤ W lam mu t := by
  rw [kb_W_first lam mu hlam hmu t]
  have : 0 ≤ ∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * lam τ :=
    intervalIntegral.integral_nonneg ht fun τ hτ =>
      mul_nonneg (Real.exp_pos _).le (hlam0 τ hτ.1)
  have := Real.exp_pos (-rho lam mu t)
  nlinarith [mul_nonneg this.le ‹0 ≤ ∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * lam τ›]

lemma kb_W_deriv (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu) (t : ℝ) :
    HasDerivAt (W lam mu) (mu t - (mu t - lam t) * W lam mu t) t := by
  have hrho := kb_hrho lam mu hlam hmu
  have hrc := kb_hrc lam mu hlam hmu
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

theorem solution (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu)
    (hlam0 : ∀ t, 0 ≤ t → 0 ≤ lam t) (hmu0 : ∀ t, 0 ≤ t → 0 ≤ mu t) :
    xi lam mu 0 = 0 ∧ eta lam mu 0 = 0 ∧
      ∀ t, 0 ≤ t → ∃ ξ' η' : ℝ,
        HasDerivAt (xi lam mu) ξ' t ∧ HasDerivAt (eta lam mu) η' t ∧
        (eta lam mu t * ξ' - xi lam mu t * η') + η' =
          lam t * (1 - xi lam mu t) * (1 - eta lam mu t) ∧
        ξ' = mu t * (1 - xi lam mu t) * (1 - eta lam mu t) := by
  have hρ0 : rho lam mu 0 = 0 := by simp [rho]
  have hW0 : W lam mu 0 = 1 := by simp [W, hρ0]
  refine ⟨by simp [xi, hW0, hρ0], by simp [eta, hW0], ?_⟩
  intro t ht
  have hW := kb_W_ge_one lam mu hlam hmu hlam0 t ht
  have hWpos : 0 < W lam mu t := by linarith
  have hWne : W lam mu t ≠ 0 := hWpos.ne'
  have hWd := kb_W_deriv lam mu hlam hmu t
  have hf : HasDerivAt (fun s => Real.exp (-rho lam mu s))
      (Real.exp (-rho lam mu t) * (-(mu t - lam t))) t :=
    ((kb_hrho lam mu hlam hmu t).neg).exp
  have hq := hf.div hWd hWne
  have hxi := hq.const_sub 1
  have hc : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 t := hasDerivAt_const t 1
  have hq2 := hc.div hWd hWne
  have heta := hq2.const_sub 1
  refine ⟨_, _, hxi, heta, ?_, ?_⟩
  · unfold xi eta
    field_simp
    ring
  · unfold xi eta
    field_simp
    ring
