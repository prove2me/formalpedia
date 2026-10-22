-- Prove2me | solution 1 for KendallBD.Sol.genFun_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:51:40.641802+00:00
-- url     : https://prove2.me/submissions/90326988-3da6-4b21-9fb9-ef531fec6491

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
    ∀ t, 0 ≤ t → ∀ z : ℝ, |z| ≤ 1 →
      HasSum (fun n : ℕ => P lam mu n t * z ^ n)
        (genFun (xi lam mu t) (eta lam mu t) z) := by
  intro t ht z hz
  have hW := kb_W_ge_one lam mu hlam hmu hlam0 t ht
  have hW0 : 0 < W lam mu t := by linarith
  have hη0 : 0 ≤ eta lam mu t := by
    unfold eta
    have : 1 / W lam mu t ≤ 1 := by rw [div_le_one hW0]; exact hW
    linarith
  have hη1 : eta lam mu t < 1 := by
    unfold eta
    have : 0 < 1 / W lam mu t := by positivity
    linarith
  have hr : |eta lam mu t * z| < 1 := by
    rw [abs_mul, abs_of_nonneg hη0]
    calc eta lam mu t * |z| ≤ eta lam mu t * 1 := by gcongr
      _ < 1 := by linarith
  have hg := (hasSum_geometric_of_abs_lt_one hr).mul_left
    ((1 - xi lam mu t) * (1 - eta lam mu t) * z)
  have hden : 1 - eta lam mu t * z ≠ 0 := by
    intro h
    have : eta lam mu t * z = 1 := by linarith
    rw [this] at hr; simp at hr
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton]
  have hP0 : P lam mu 0 t * z ^ 0 = xi lam mu t := by simp [P]
  rw [hP0]
  have heq : genFun (xi lam mu t) (eta lam mu t) z - xi lam mu t =
      (1 - xi lam mu t) * (1 - eta lam mu t) * z * (1 - eta lam mu t * z)⁻¹ := by
    unfold genFun
    field_simp
    ring
  rw [heq]
  have hf : (fun n : ℕ => P lam mu (n + 1) t * z ^ (n + 1)) =
      fun i : ℕ => (1 - xi lam mu t) * (1 - eta lam mu t) * z * (eta lam mu t * z) ^ i := by
    funext n
    simp only [P, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
    rw [mul_pow, pow_succ]
    ring
  rw [hf]
  exact hg
