-- Prove2me | solution 1 for LyapDiffMC.RandomHorizon.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:33:40.623016+00:00
-- url     : https://prove2.me/submissions/691c6b33-9e06-4d46-bc32-a3dc754189e8

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

theorem solution {S : Type*} [MeasurableSpace S] (Q : Kernel S S)
    (f v : S → ℝ≥0∞) (_hf : Measurable f) (hv : Measurable v) (_hv_fin : ∀ x, v x ≠ ⊤)
    (h315 : ∀ x, ∫⁻ y, v y ∂(Q x) + f x ≤ v x) :
    ∀ x, ∑' n, ∫⁻ y, f y ∂(Qpow Q n x) ≤ v x := by
  intro x
  exact prop31_gen Q Set.univ MeasurableSet.univ (by simp) f v hv (fun x _ => h315 x) x trivial
