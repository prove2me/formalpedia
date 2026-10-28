-- Prove2me | solution 1 for LyapDiffMC.RandomHorizon.eq_3_24
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:34:40.182866+00:00
-- url     : https://prove2.me/submissions/9681152a-dda1-49f5-a0c0-cb99494dba0e

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LyapDiffMC.RandomHorizon

lemma Qpow_conc {S : Type*} [MeasurableSpace S] (Q : Kernel S S) (C : Set S)
    (hC : MeasurableSet C) (hQ : ∀ y, Q y Cᶜ = 0) :
    ∀ n, ∀ x ∈ C, Qpow Q n x Cᶜ = 0 := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp only [Qpow, Kernel.id_apply]
    rw [Measure.dirac_apply' _ hC.compl]
    simp [hx]
  | succ n ih =>
    intro x hx
    simp only [Qpow]
    rw [Kernel.comp_apply' _ _ _ hC.compl]
    simp [hQ]

lemma prop31_gen {S : Type*} [MeasurableSpace S] (Q : Kernel S S) (C : Set S)
    (hC : MeasurableSet C) (hQ : ∀ y, Q y Cᶜ = 0)
    (f v : S → ℝ≥0∞) (hv : Measurable v)
    (h315 : ∀ x ∈ C, ∫⁻ y, v y ∂(Q x) + f x ≤ v x) :
    ∀ x ∈ C, ∑' n, ∫⁻ y, f y ∂(Qpow Q n x) ≤ v x := by
  have key : ∀ N, ∀ x ∈ C,
      (∑ n ∈ Finset.range N, ∫⁻ y, f y ∂(Qpow Q n x)) + ∫⁻ y, v y ∂(Qpow Q N x) ≤ v x := by
    intro N
    induction N with
    | zero =>
      intro x hx
      simp [Qpow, Kernel.id_apply, lintegral_dirac' _ hv]
    | succ N ih =>
      intro x hx
      have hQv : Measurable fun y => ∫⁻ z, v z ∂(Q y) := hv.lintegral_kernel
      have e1 : ∫⁻ y, v y ∂(Qpow Q (N+1) x) = ∫⁻ y, (∫⁻ z, v z ∂(Q y)) ∂(Qpow Q N x) := by
        simp only [Qpow]
        rw [Kernel.lintegral_comp _ _ _ hv]
      have e2 : ∫⁻ y, f y ∂(Qpow Q N x) + ∫⁻ y, (∫⁻ z, v z ∂(Q y)) ∂(Qpow Q N x)
          ≤ ∫⁻ y, v y ∂(Qpow Q N x) := by
        rw [← lintegral_add_right' _ hQv.aemeasurable]
        apply lintegral_mono_ae
        have hc := Qpow_conc Q C hC hQ N x hx
        have : ∀ᵐ y ∂(Qpow Q N x), y ∈ C := by
          rw [ae_iff]; exact hc
        filter_upwards [this] with y hy
        rw [add_comm]; exact h315 y hy
      calc (∑ n ∈ Finset.range (N+1), ∫⁻ y, f y ∂(Qpow Q n x)) + ∫⁻ y, v y ∂(Qpow Q (N+1) x)
          = (∑ n ∈ Finset.range N, ∫⁻ y, f y ∂(Qpow Q n x)) +
              (∫⁻ y, f y ∂(Qpow Q N x) + ∫⁻ y, (∫⁻ z, v z ∂(Q y)) ∂(Qpow Q N x)) := by
            rw [Finset.sum_range_succ, e1, add_assoc]
        _ ≤ (∑ n ∈ Finset.range N, ∫⁻ y, f y ∂(Qpow Q n x)) + ∫⁻ y, v y ∂(Qpow Q N x) := by
            gcongr
        _ ≤ v x := ih x hx
  intro x hx
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => le_trans le_self_add (key N x hx)

lemma KC_compl {S : Type*} [MeasurableSpace S] (M : Setting S) (θ : ℝ) (y : S) :
    KC M θ y M.Cᶜ = 0 := by
  rw [KC, Kernel.restrict_apply' _ _ _ M.C_meas.compl]
  simp

lemma KC_lintegral {S : Type*} [MeasurableSpace S] (M : Setting S) (θ : ℝ) (y : S)
    (v : S → ℝ≥0∞) : ∫⁻ z, v z ∂(KC M θ y) = ∫⁻ z in M.C, v z ∂(discKernel M θ y) := by
  rw [KC, Kernel.restrict_apply]

lemma green_bound {S : Type*} [MeasurableSpace S] (M : Setting S) (θ : ℝ)
    (F v : S → ℝ≥0∞) (hv : Measurable v)
    (h : ∀ x ∈ M.C, ∫⁻ y in M.C, v y ∂(discKernel M θ x) + F x ≤ v x) :
    ∀ x ∈ M.C, ∫⁻ y, F y ∂(greenMeasure M θ x) ≤ v x := by
  intro x hx
  rw [greenMeasure, lintegral_sum_measure]
  exact prop31_gen (KC M θ) M.C M.C_meas (KC_compl M θ) F v hv
    (fun x hx => by rw [KC_lintegral]; exact h x hx) x hx

theorem solution {S : Type*} [MeasurableSpace S] (M : Setting S)
    (θ₀ ε : ℝ) (hε : 0 < ε) (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Icc (θ₀ - ε) (θ₀ + ε), Measurable (Function.uncurry (k θ)))
    (hA2 : ∀ x ∈ M.C, ∀ y, ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)))
    (v₀ v₁ : S → ℝ) (hv₀ : Measurable v₀) (hv₁ : Measurable v₁)
    (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x) (hv₁_nn : ∀ x ∈ M.C, 0 ≤ v₁ x)
    (h312 : ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₁ y) ∂(discKernel M θ₀ x)
        + ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₀ y) ∂(discKernel M θ₀ x)
        + rtilde M k θ₀ ε x ≤ ENNReal.ofReal (v₁ x)) :
    ∀ x ∈ M.C,
      ∫⁻ y, (∫⁻ z in M.C, omega k θ₀ ε y z * ENNReal.ofReal (v₀ z) ∂(discKernel M θ₀ y)
          + ∫⁻ z in M.Cᶜ, omega k θ₀ ε y z * ‖M.f z‖ₑ ∂(discKernel M θ₀ y))
        ∂(greenMeasure M θ₀ x) < ⊤ := by
  intro x hx
  refine lt_of_le_of_lt (green_bound M θ₀ _ _ hv₁.ennreal_ofReal ?_ x hx) ENNReal.ofReal_lt_top
  intro y hy
  have := h312 y hy
  rw [add_assoc] at this
  exact this
