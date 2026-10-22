-- Prove2me | solution 1 for KendallBD.Sol.geometric_solution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:07:40.720892+00:00
-- url     : https://prove2.me/submissions/efa73dad-367a-40a9-adfe-150940213db8

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

lemma kb_xi_eta_deriv (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu)
    (hlam0 : ∀ t, 0 ≤ t → 0 ≤ lam t) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (xi lam mu) (mu t * (1 - xi lam mu t) * (1 - eta lam mu t)) t ∧
    HasDerivAt (eta lam mu) ((1 - eta lam mu t) * (lam t - mu t * eta lam mu t)) t := by
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
  constructor
  · refine hxi.congr_deriv ?_
    unfold xi eta
    field_simp
    ring
  · refine heta.congr_deriv ?_
    unfold eta
    field_simp
    ring

lemma kb_xi_range (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu)
    (hlam0 : ∀ t, 0 ≤ t → 0 ≤ lam t) (hmu0 : ∀ t, 0 ≤ t → 0 ≤ mu t) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ xi lam mu t ∧ xi lam mu t < 1 ∧ 0 ≤ eta lam mu t ∧ eta lam mu t < 1 := by
  have hW := kb_W_ge_one lam mu hlam hmu hlam0 t ht
  have hWpos : 0 < W lam mu t := by linarith
  have hEpos := Real.exp_pos (-rho lam mu t)
  have hM : 0 ≤ ∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * mu τ :=
    intervalIntegral.integral_nonneg ht fun τ hτ => mul_nonneg (Real.exp_pos _).le (hmu0 τ hτ.1)
  have hWE : Real.exp (-rho lam mu t) ≤ W lam mu t := by
    have : W lam mu t = Real.exp (-rho lam mu t) *
        (1 + ∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * mu τ) := rfl
    rw [this]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold xi
    have : Real.exp (-rho lam mu t) / W lam mu t ≤ 1 := (div_le_one hWpos).2 hWE
    linarith
  · unfold xi
    have : 0 < Real.exp (-rho lam mu t) / W lam mu t := by positivity
    linarith
  · unfold eta
    have : 1 / W lam mu t ≤ 1 := (div_le_one hWpos).2 hW
    linarith
  · unfold eta
    have : 0 < 1 / W lam mu t := by positivity
    linarith

theorem solution (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu)
    (hlam0 : ∀ t, 0 ≤ t → 0 ≤ lam t) (hmu0 : ∀ t, 0 ≤ t → 0 ≤ mu t) :
    InitialCondition (P lam mu) ∧ SolvesForward lam mu (P lam mu) ∧
      ∀ t, 0 ≤ t → (∀ n, 0 ≤ P lam mu n t) ∧
        HasSum (fun n : ℕ => P lam mu n t) 1 := by
  have hρ0 : rho lam mu 0 = 0 := by simp [rho]
  have hW0 : W lam mu 0 = 1 := by simp [W, hρ0]
  have hxi0 : xi lam mu 0 = 0 := by simp [xi, hW0, hρ0]
  have heta0 : eta lam mu 0 = 0 := by simp [eta, hW0]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simp [P, hxi0, heta0]
    · intro n hn
      by_cases h0 : n = 0
      · simp [P, h0, hxi0]
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        simp [P, heta0]
  · refine ⟨?_, ?_⟩
    · intro t ht
      have h := (kb_xi_eta_deriv lam mu hlam hmu hlam0 t ht).1
      have e : (fun s => P lam mu 0 s) = xi lam mu := by funext s; simp [P]
      rw [e]
      convert h using 1
      simp [P]
      ring
    · intro n hn t ht
      obtain ⟨hx, he⟩ := kb_xi_eta_deriv lam mu hlam hmu hlam0 t ht
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hPk : ∀ s, P lam mu (k + 1) s =
          (1 - xi lam mu s) * (1 - eta lam mu s) * eta lam mu s ^ k := by
        intro s; simp [P]
      have e : (fun s => P lam mu (k + 1) s) = fun s =>
          (1 - xi lam mu s) * (1 - eta lam mu s) * eta lam mu s ^ k := funext hPk
      have h1 : HasDerivAt (fun s => 1 - xi lam mu s)
          (-(mu t * (1 - xi lam mu t) * (1 - eta lam mu t))) t := by
        exact ((hasDerivAt_const t (1:ℝ)).sub hx).congr_deriv (by ring)
      have h2 : HasDerivAt (fun s => 1 - eta lam mu s)
          (-((1 - eta lam mu t) * (lam t - mu t * eta lam mu t))) t := by
        exact ((hasDerivAt_const t (1:ℝ)).sub he).congr_deriv (by ring)
      have h3 : HasDerivAt (fun s => eta lam mu s ^ k)
          (k * eta lam mu t ^ (k - 1) * ((1 - eta lam mu t) * (lam t - mu t * eta lam mu t))) t :=
        he.pow k
      have hd := (h1.mul h2).mul h3
      rw [e]
      refine hd.congr_deriv ?_
      simp only [Pi.mul_apply]
      have hs : ∀ m : ℕ, P lam mu (m + 1) t =
          (1 - xi lam mu t) * (1 - eta lam mu t) * eta lam mu t ^ m := by
        intro m; simp [P]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [P]
        ring
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have h3' : j + 1 + 1 - 1 = j + 1 := rfl
        rw [h3']
        simp only [hs, Nat.add_sub_cancel]
        push_cast
        ring
  · intro t ht
    obtain ⟨hx0, hx1, hη0, hη1⟩ := kb_xi_range lam mu hlam hmu hlam0 hmu0 t ht
    constructor
    · intro n
      by_cases h0 : n = 0
      · simp [P, h0, hx0]
      · simp only [P, h0, if_false]
        have : 0 ≤ 1 - xi lam mu t := by linarith
        have : 0 < 1 - eta lam mu t := by linarith
        positivity
    · have hr : |eta lam mu t| < 1 := by rw [abs_of_nonneg hη0]; exact hη1
      have hg := (hasSum_geometric_of_abs_lt_one hr).mul_left
        ((1 - xi lam mu t) * (1 - eta lam mu t))
      rw [← hasSum_nat_add_iff' 1]
      simp only [Finset.range_one, Finset.sum_singleton]
      have hP0 : P lam mu 0 t = xi lam mu t := by simp [P]
      rw [hP0]
      have hf : (fun n : ℕ => P lam mu (n + 1) t) =
          fun i : ℕ => (1 - xi lam mu t) * (1 - eta lam mu t) * eta lam mu t ^ i := by
        funext n; simp [P]
      rw [hf]
      have hden : (1 - eta lam mu t) ≠ 0 := by linarith
      have e2 : (1 - xi lam mu t) * (1 - eta lam mu t) * (1 - eta lam mu t)⁻¹
          = 1 - xi lam mu t := by field_simp
      rw [e2] at hg
      exact hg
