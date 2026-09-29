-- Prove2me | solution 1 for LangevinHarmonicTrap.msd_ode
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T20:24:56.786129+00:00
-- url     : https://prove2.me/submissions/ac4ca032-e3a5-4e22-ba2c-9ca77630221d

import Mathlib
import Definitions.Def_LangevinHarmonicTrap_dotSum
import Definitions.Def_LangevinHarmonicTrap_IsLangevinPath

open Real Filter Topology Finset MeasureTheory
open LangevinHarmonicTrap

theorem W2m_LangevinHarmonicTrap_sqDisp_hasDerivAt {d : ℕ} {m zeta k : ℝ}
    {x v a f : Fin d → ℝ → ℝ}
    (h : IsLangevinPath d m zeta k x v a f) :
    (∀ t : ℝ, HasDerivAt (dotSum d x x) (2 * dotSum d x v t) t) ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => 2 * dotSum d x v s)
        (2 * (dotSum d v v t + dotSum d x a t)) t) := by
  constructor
  · intro t
    have H : HasDerivAt (fun s => ∑ i : Fin d, x i s * x i s)
        (∑ i : Fin d, (v i t * x i t + x i t * v i t)) t :=
      HasDerivAt.fun_sum fun i _ => (h.hasDerivAt_pos i t).fun_mul (h.hasDerivAt_pos i t)
    refine H.congr_deriv ?_
    simp only [dotSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · intro t
    have H : HasDerivAt (fun s => ∑ i : Fin d, x i s * v i s)
        (∑ i : Fin d, (v i t * v i t + x i t * a i t)) t :=
      HasDerivAt.fun_sum fun i _ => (h.hasDerivAt_pos i t).fun_mul (h.hasDerivAt_vel i t)
    refine (H.const_mul 2).congr_deriv ?_
    simp only [dotSum, Finset.sum_add_distrib]

theorem W2m_LangevinHarmonicTrap_key {d : ℕ} {m zeta k : ℝ} {x v a f : Fin d → ℝ → ℝ}
    (h : IsLangevinPath d m zeta k x v a f) (t : ℝ) :
    dotSum d x f t = m * dotSum d x a t + zeta * dotSum d x v t + k * dotSum d x x t := by
  simp only [dotSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := h.newton i t
  linear_combination (-(x i t)) * this

theorem W2m_LangevinHarmonicTrap_pathwise_identity {d : ℕ} {m zeta k : ℝ}
    {x v a f : Fin d → ℝ → ℝ}
    (h : IsLangevinPath d m zeta k x v a f)
    (S S1 S2 : ℝ → ℝ)
    (hS : ∀ t : ℝ, S t = dotSum d x x t)
    (hS1 : ∀ t : ℝ, HasDerivAt S (S1 t) t)
    (hS2 : ∀ t : ℝ, HasDerivAt S1 (S2 t) t) :
    ∀ t : ℝ, m / 2 * S2 t + zeta / 2 * S1 t + k * S t
      = m * dotSum d v v t + dotSum d x f t := by
  obtain ⟨h1, h2⟩ := W2m_LangevinHarmonicTrap_sqDisp_hasDerivAt h
  have eS : S = dotSum d x x := funext hS
  have hS' : ∀ t, S1 t = 2 * dotSum d x v t := by
    intro t
    have H : HasDerivAt S (2 * dotSum d x v t) t := by rw [eS]; exact h1 t
    exact (hS1 t).unique H
  have e1 : S1 = fun s => 2 * dotSum d x v s := funext hS'
  have hS2' : ∀ t, S2 t = 2 * (dotSum d v v t + dotSum d x a t) := by
    intro t
    have H := hS2 t
    rw [e1] at H
    exact H.unique (h2 t)
  intro t
  rw [hS t, hS' t, hS2' t, W2m_LangevinHarmonicTrap_key h t]
  ring

theorem W2m_LangevinHarmonicTrap_ensemble_averaged_identity {d : ℕ} {m zeta k : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {x v a f : Ω → Fin d → ℝ → ℝ}
    (hdyn : ∀ w : Ω, IsLangevinPath d m zeta k (x w) (v w) (a w) (f w))
    (M M1 M2 : ℝ → ℝ)
    (hM : ∀ t : ℝ, M t = ∫ w, dotSum d (x w) (x w) t ∂mu)
    (hM1 : ∀ t : ℝ, M1 t = ∫ w, 2 * dotSum d (x w) (v w) t ∂mu)
    (hM2 : ∀ t : ℝ, M2 t = ∫ w, 2 * (dotSum d (v w) (v w) t + dotSum d (x w) (a w) t) ∂mu)
    (hxx : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (x w) t) mu)
    (hxv : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (v w) t) mu)
    (hvv : ∀ t : ℝ, Integrable (fun w => dotSum d (v w) (v w) t) mu)
    (hxa : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (a w) t) mu) :
    ∀ t : ℝ, m / 2 * M2 t + zeta / 2 * M1 t + k * M t
      = m * (∫ w, dotSum d (v w) (v w) t ∂mu) + ∫ w, dotSum d (x w) (f w) t ∂mu := by
  intro t
  have hp : ∀ w, dotSum d (x w) (f w) t = m * dotSum d (x w) (a w) t
      + zeta * dotSum d (x w) (v w) t + k * dotSum d (x w) (x w) t :=
    fun w => W2m_LangevinHarmonicTrap_key (hdyn w) t
  have A1 : ∫ w, 2 * (dotSum d (v w) (v w) t + dotSum d (x w) (a w) t) ∂mu
      = 2 * ((∫ w, dotSum d (v w) (v w) t ∂mu) + ∫ w, dotSum d (x w) (a w) t ∂mu) := by
    rw [integral_const_mul, integral_add (hvv t) (hxa t)]
  have A2 : ∫ w, 2 * dotSum d (x w) (v w) t ∂mu = 2 * ∫ w, dotSum d (x w) (v w) t ∂mu :=
    integral_const_mul _ _
  have A3 : ∫ w, dotSum d (x w) (f w) t ∂mu
      = m * (∫ w, dotSum d (x w) (a w) t ∂mu) + zeta * (∫ w, dotSum d (x w) (v w) t ∂mu)
        + k * ∫ w, dotSum d (x w) (x w) t ∂mu := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hp), integral_add, integral_add,
      integral_const_mul, integral_const_mul, integral_const_mul]
    all_goals first
      | exact ((hxa t).const_mul m).add ((hxv t).const_mul zeta)
      | exact (hxx t).const_mul k
      | exact (hxa t).const_mul m
      | exact (hxv t).const_mul zeta
  rw [hM t, hM1 t, hM2 t, A1, A2, A3]
  ring

theorem solution {d : ℕ} {m zeta k kB T : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {x v a f : Ω → Fin d → ℝ → ℝ}
    (hdyn : ∀ w : Ω, IsLangevinPath d m zeta k (x w) (v w) (a w) (f w))
    (M M1 M2 : ℝ → ℝ)
    (hM : ∀ t : ℝ, M t = ∫ w, dotSum d (x w) (x w) t ∂mu)
    (hM1 : ∀ t : ℝ, M1 t = ∫ w, 2 * dotSum d (x w) (v w) t ∂mu)
    (hM2 : ∀ t : ℝ, M2 t = ∫ w, 2 * (dotSum d (v w) (v w) t + dotSum d (x w) (a w) t) ∂mu)
    (hMderiv : ∀ t : ℝ, HasDerivAt M (M1 t) t)
    (hM1deriv : ∀ t : ℝ, HasDerivAt M1 (M2 t) t)
    (hxx : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (x w) t) mu)
    (hxv : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (v w) t) mu)
    (hvv : ∀ t : ℝ, Integrable (fun w => dotSum d (v w) (v w) t) mu)
    (hxa : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (a w) t) mu)
    (hnoise : ∀ t : ℝ, ∫ w, dotSum d (x w) (f w) t ∂mu = 0)
    (hequip : ∀ t : ℝ, m * ∫ w, dotSum d (v w) (v w) t ∂mu = d * kB * T) :
    ∀ t : ℝ, m * deriv (deriv M) t + zeta * deriv M t + 2 * k * M t
      = 2 * (d * kB * T) := by
  have hid := W2m_LangevinHarmonicTrap_ensemble_averaged_identity hdyn M M1 M2 hM hM1 hM2
    hxx hxv hvv hxa
  have e1 : deriv M = M1 := funext fun t => (hMderiv t).deriv
  have e2 : deriv M1 = M2 := funext fun t => (hM1deriv t).deriv
  intro t
  rw [e1, e2]
  have H := hid t
  rw [hnoise t] at H
  linear_combination 2 * H + 2 * hequip t

theorem W2m_LangevinHarmonicTrap_msd_overdamped {d : ℕ} {zeta k kB T : ℝ} (hzeta : 0 < zeta)
    (hk : 0 < k)
    (M M1 : ℝ → ℝ)
    (hM : ∀ t : ℝ, M t = d * kB * T / k * (1 - Real.exp (-(2 * k / zeta) * t)))
    (hM1 : ∀ t : ℝ, M1 t = 2 * (d * kB * T) / zeta * Real.exp (-(2 * k / zeta) * t)) :
    (∀ t : ℝ, HasDerivAt M (M1 t) t) ∧
      (∀ t : ℝ, zeta * M1 t + 2 * k * M t = 2 * (d * kB * T)) ∧
      M 0 = 0 ∧ M1 0 = 2 * (d * kB * T) / zeta ∧
      Tendsto M atTop (𝓝 (d * kB * T / k)) := by
  have hk0 : k ≠ 0 := hk.ne'
  have hz0 : zeta ≠ 0 := hzeta.ne'
  have eM : M = fun t => d * kB * T / k * (1 - Real.exp (-(2 * k / zeta) * t)) := funext hM
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [eM, hM1 t]
    have h1 : HasDerivAt (fun t => -(2 * k / zeta) * t) (-(2 * k / zeta)) t :=
      hasDerivAt_const_mul _
    have h2 := (h1.exp.const_sub 1).const_mul (d * kB * T / k)
    refine h2.congr_deriv ?_
    first | (field_simp; ring1) | field_simp | ring1
  · intro t
    rw [hM t, hM1 t]
    first | (field_simp; ring1) | field_simp | ring1
  · rw [hM 0]; simp
  · rw [hM1 0]; simp
  · rw [eM]
    have hneg : -(2 * k / zeta) < 0 := by
      have : 0 < 2 * k / zeta := by positivity
      linarith
    have H : Tendsto (fun t => Real.exp (-(2 * k / zeta) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg hneg tendsto_id)
    have H2 := (H.const_sub 1).const_mul (d * kB * T / k)
    simpa using H2

theorem W2m_LangevinHarmonicTrap_msd_solution {d : ℕ} {m zeta k kB T lamP lamM : ℝ}
    (hk : k ≠ 0) (hne : lamP ≠ lamM)
    (hrootP : m * lamP ^ 2 + zeta * lamP + 2 * k = 0)
    (hrootM : m * lamM ^ 2 + zeta * lamM + 2 * k = 0)
    (M M1 M2 : ℝ → ℝ)
    (hM : ∀ t : ℝ, M t = d * kB * T / k *
      (1 + (lamM * Real.exp (lamP * t) - lamP * Real.exp (lamM * t)) / (lamP - lamM)))
    (hM1 : ∀ t : ℝ, M1 t = d * kB * T / k *
      (lamP * lamM * (Real.exp (lamP * t) - Real.exp (lamM * t)) / (lamP - lamM)))
    (hM2 : ∀ t : ℝ, M2 t = d * kB * T / k *
      (lamP * lamM * (lamP * Real.exp (lamP * t) - lamM * Real.exp (lamM * t))
        / (lamP - lamM))) :
    (∀ t : ℝ, HasDerivAt M (M1 t) t) ∧ (∀ t : ℝ, HasDerivAt M1 (M2 t) t) ∧
      (∀ t : ℝ, m * M2 t + zeta * M1 t + 2 * k * M t = 2 * (d * kB * T)) ∧
      M 0 = 0 ∧ M1 0 = 0 := by
  have hΔ : lamP - lamM ≠ 0 := sub_ne_zero.mpr hne
  have eM : M = fun t => d * kB * T / k *
      (1 + (lamM * Real.exp (lamP * t) - lamP * Real.exp (lamM * t)) / (lamP - lamM)) :=
    funext hM
  have eM1 : M1 = fun t => d * kB * T / k *
      (lamP * lamM * (Real.exp (lamP * t) - Real.exp (lamM * t)) / (lamP - lamM)) :=
    funext hM1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [eM, hM1 t]
    have hp := ((hasDerivAt_id' t).const_mul lamP).exp
    have hm := ((hasDerivAt_id' t).const_mul lamM).exp
    have H := ((((hp.const_mul lamM).fun_sub (hm.const_mul lamP)).div_const
      (lamP - lamM)).const_add 1).const_mul (d * kB * T / k)
    refine H.congr_deriv ?_
    ring
  · intro t
    rw [eM1, hM2 t]
    have hp := ((hasDerivAt_id' t).const_mul lamP).exp
    have hm := ((hasDerivAt_id' t).const_mul lamM).exp
    have H := ((((hp.fun_sub hm).const_mul (lamP * lamM)).div_const (lamP - lamM))).const_mul
      (d * kB * T / k)
    refine H.congr_deriv ?_
    ring
  · intro t
    rw [hM t, hM1 t, hM2 t]
    have key : m * (d * kB * T / k * (lamP * lamM * (lamP * Real.exp (lamP * t)
          - lamM * Real.exp (lamM * t)) / (lamP - lamM)))
        + zeta * (d * kB * T / k * (lamP * lamM * (Real.exp (lamP * t)
          - Real.exp (lamM * t)) / (lamP - lamM)))
        + 2 * k * (d * kB * T / k * (1 + (lamM * Real.exp (lamP * t)
          - lamP * Real.exp (lamM * t)) / (lamP - lamM)))
        - 2 * (d * kB * T)
        = d * kB * T / k / (lamP - lamM) *
          (lamM * Real.exp (lamP * t) * (m * lamP ^ 2 + zeta * lamP + 2 * k)
            - lamP * Real.exp (lamM * t) * (m * lamM ^ 2 + zeta * lamM + 2 * k)) := by
      first | (field_simp; ring1) | field_simp
    rw [hrootP, hrootM] at key
    simp only [mul_zero, sub_zero] at key
    linarith
  · rw [hM 0]
    have : (lamM - lamP) / (lamP - lamM) = -1 := by
      rw [div_eq_iff hΔ]; ring
    simp only [mul_zero, Real.exp_zero, mul_one, this]
    ring
  · rw [hM1 0]; simp
