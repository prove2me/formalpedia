-- Prove2me | solution 1 for LyapDiffMC.RandomHorizon.proof_3_1_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:59:41.681514+00:00
-- url     : https://prove2.me/submissions/d1b9ac36-5d8b-484f-8bed-933618e6778f

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon.Aux

open LyapDiffMC.RandomHorizon

variable {S : Type*} [MeasurableSpace S]

instance discKernel_sfinite (M : Setting S) (θ : ℝ) : IsSFiniteKernel (discKernel M θ) := by
  unfold discKernel
  exact Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

instance KC_sfinite (M : Setting S) (θ : ℝ) : IsSFiniteKernel (KC M θ) := by
  unfold KC; infer_instance

instance Qpow_sfinite (Q : Kernel S S) [IsSFiniteKernel Q] (n : ℕ) :
    IsSFiniteKernel (Qpow Q n) := by
  induction n with
  | zero => simp only [Qpow]; infer_instance
  | succ n ih => simp only [Qpow]; infer_instance

instance kpow_sfinite (M : Setting S) (θ : ℝ) (n : ℕ) : IsSFiniteKernel (kpow M θ n) := by
  unfold kpow; infer_instance

/-- The Green kernel `G(θ) = Σₙ Kⁿ(θ)`. -/
noncomputable def greenK (M : Setting S) (θ : ℝ) : Kernel S S := Kernel.sum (kpow M θ)

instance greenK_sfinite (M : Setting S) (θ : ℝ) : IsSFiniteKernel (greenK M θ) := by
  unfold greenK; infer_instance

lemma greenMeasure_eq (M : Setting S) (θ : ℝ) (x : S) :
    greenMeasure M θ x = greenK M θ x := by
  rw [greenK, Kernel.sum_apply]; rfl

lemma Qpow_succ' (Q : Kernel S S) (n : ℕ) : Qpow Q (n + 1) = Qpow Q n ∘ₖ Q := by
  induction n with
  | zero => simp [Qpow, Kernel.comp_id, Kernel.id_comp]
  | succ n ih =>
    calc Qpow Q (n + 1 + 1) = Q ∘ₖ Qpow Q (n + 1) := rfl
      _ = Q ∘ₖ (Qpow Q n ∘ₖ Q) := by rw [ih]
      _ = (Q ∘ₖ Qpow Q n) ∘ₖ Q := (Kernel.comp_assoc _ _ _).symm
      _ = Qpow Q (n + 1) ∘ₖ Q := rfl

lemma kernel_sum_nat (κ : ℕ → Kernel S S) :
    Kernel.sum κ = κ 0 + Kernel.sum (fun n => κ (n + 1)) := by
  ext x s hs
  rw [Kernel.add_apply, Measure.add_apply, Kernel.sum_apply' _ _ hs, Kernel.sum_apply' _ _ hs]
  exact tsum_eq_zero_add' ENNReal.summable

lemma greenK_first_step (M : Setting S) (θ : ℝ) :
    greenK M θ = Kernel.id + greenK M θ ∘ₖ KC M θ := by
  rw [greenK, Kernel.comp_sum_left, kernel_sum_nat (kpow M θ)]
  congr 1
  congr 1
  funext n
  rw [kpow, kpow, Qpow_succ']

lemma KC_apply (M : Setting S) (θ : ℝ) (x : S) :
    KC M θ x = (discKernel M θ x).restrict M.C := by
  rw [KC, Kernel.restrict_apply]

lemma Qpow_conc (Q : Kernel S S) (C : Set S)
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

lemma prop31_gen (Q : Kernel S S) (C : Set S)
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

lemma KC_compl (M : Setting S) (θ : ℝ) (y : S) :
    KC M θ y M.Cᶜ = 0 := by
  rw [KC, Kernel.restrict_apply' _ _ _ M.C_meas.compl]
  simp

lemma KC_lintegral (M : Setting S) (θ : ℝ) (y : S)
    (v : S → ℝ≥0∞) : ∫⁻ z, v z ∂(KC M θ y) = ∫⁻ z in M.C, v z ∂(discKernel M θ y) := by
  rw [KC, Kernel.restrict_apply]

/-- Proposition 3.1 for the Green measure. -/
lemma green_bound (M : Setting S) (θ : ℝ)
    (F v : S → ℝ≥0∞) (hv : Measurable v)
    (h : ∀ x ∈ M.C, ∫⁻ y in M.C, v y ∂(discKernel M θ x) + F x ≤ v x) :
    ∀ x ∈ M.C, ∫⁻ y, F y ∂(greenMeasure M θ x) ≤ v x := by
  intro x hx
  rw [greenMeasure, lintegral_sum_measure]
  exact prop31_gen (KC M θ) M.C M.C_meas (KC_compl M θ) F v hv
    (fun x hx => by rw [KC_lintegral]; exact h x hx) x hx

/-- For `x ∈ C`, `G(θ, x, ·)` is concentrated on `C`. -/
lemma greenMeasure_compl (M : Setting S) (θ : ℝ) (x : S) (hx : x ∈ M.C) :
    greenMeasure M θ x M.Cᶜ = 0 := by
  rw [greenMeasure, Measure.sum_apply _ M.C_meas.compl]
  simp only [ENNReal.tsum_eq_zero]
  intro n
  exact Qpow_conc (KC M θ) M.C M.C_meas (KC_compl M θ) n x hx

lemma ae_green_mem (M : Setting S) (θ : ℝ) (x : S) (hx : x ∈ M.C) :
    ∀ᵐ y ∂(greenMeasure M θ x), y ∈ M.C := by
  rw [ae_iff]; exact greenMeasure_compl M θ x hx

lemma ftilde_sm (M : Setting S) (θ : ℝ) : StronglyMeasurable (ftilde M θ) := by
  have h1 : StronglyMeasurable fun y => ∫ z, M.f z ∂((discKernel M θ).restrict M.C_meas.compl y) :=
    StronglyMeasurable.integral_kernel_prod_right'
      (f := fun p : S × S => M.f p.2) (M.f_meas.comp measurable_snd).stronglyMeasurable
  have h2 : (fun y => ∫ z, M.f z ∂((discKernel M θ).restrict M.C_meas.compl y))
      = fun y => ∫ z in M.Cᶜ, M.f z ∂(discKernel M θ y) := by
    funext y; rw [Kernel.restrict_apply]
  rw [h2] at h1
  exact M.f_meas.stronglyMeasurable.add h1

lemma uStar_sm (M : Setting S) (θ : ℝ) : StronglyMeasurable (uStar M θ) := by
  have h1 : StronglyMeasurable fun y => ∫ z, ftilde M θ z ∂(greenK M θ y) :=
    StronglyMeasurable.integral_kernel_prod_right'
      (f := fun p : S × S => ftilde M θ p.2) ((ftilde_sm M θ).comp_measurable measurable_snd)
  have h2 : (fun y => ∫ z, ftilde M θ z ∂(greenK M θ y)) = uStar M θ := by
    funext y; rw [uStar, greenMeasure_eq]
  rwa [h2] at h1

lemma dirac_le_green (M : Setting S) (θ : ℝ) (x : S) :
    Measure.dirac x ≤ greenMeasure M θ x := by
  rw [greenMeasure_eq, greenK_first_step, Kernel.add_apply, Kernel.id_apply]
  exact Measure.le_add_right le_rfl

lemma comp_le_green (M : Setting S) (θ : ℝ) (x : S) :
    (greenK M θ ∘ₖ KC M θ) x ≤ greenMeasure M θ x := by
  rw [greenMeasure_eq]
  conv_rhs => rw [greenK_first_step M θ]
  rw [Kernel.add_apply]
  exact Measure.le_add_left le_rfl

/-- First-step decomposition of a `G(θ, x, ·)`-integral. -/
lemma green_integral_first_step (M : Setting S) (θ : ℝ) (F : S → ℝ) (hF : StronglyMeasurable F)
    (x : S) (hint : Integrable F (greenMeasure M θ x)) :
    ∫ y, F y ∂(greenMeasure M θ x)
      = F x + ∫ y in M.C, (∫ z, F z ∂(greenMeasure M θ y)) ∂(discKernel M θ x) := by
  have e : greenMeasure M θ x = Measure.dirac x + (greenK M θ ∘ₖ KC M θ) x := by
    rw [greenMeasure_eq]
    conv_lhs => rw [greenK_first_step M θ]
    rw [Kernel.add_apply, Kernel.id_apply]
  have hi2 : Integrable F ((greenK M θ ∘ₖ KC M θ) x) := hint.mono_measure (comp_le_green M θ x)
  have hi1 : Integrable F (Measure.dirac x) := hint.mono_measure (dirac_le_green M θ x)
  rw [e, integral_add_measure hi1 hi2, integral_dirac' _ _ hF, Kernel.integral_comp hi2,
    KC_apply]
  simp_rw [greenMeasure_eq]

lemma enorm_le_ofReal_iff_abs (u v : ℝ) (hv : 0 ≤ v) : ‖u‖ₑ ≤ ENNReal.ofReal v ↔ |u| ≤ v := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff hv]

/-- The first step of the proof of Theorem 3.1. -/
theorem bound_main (M : Setting S)
    (θ₀ ε : ℝ)
    (v₀ : S → ℝ) (hv₀ : Measurable v₀) (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x)
    (h311 : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₀ y) ∂(discKernel M θ x) + ‖ftilde M θ x‖ₑ
        ≤ ENNReal.ofReal (v₀ x)) :
    ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y, ‖ftilde M θ y‖ₑ ∂(greenMeasure M θ x) ≤ ENNReal.ofReal (v₀ x) ∧
      Integrable (ftilde M θ) (greenMeasure M θ x) ∧
      |uStar M θ x| ≤ v₀ x ∧
      IntegrableOn (uStar M θ) M.C (discKernel M θ x) ∧
      uStar M θ x = ftilde M θ x + ∫ y in M.C, uStar M θ y ∂(discKernel M θ x) := by
  intro θ hθ
  have hA : ∀ x ∈ M.C, ∫⁻ y, ‖ftilde M θ y‖ₑ ∂(greenMeasure M θ x) ≤ ENNReal.ofReal (v₀ x) :=
    green_bound M θ (fun y => ‖ftilde M θ y‖ₑ) (fun y => ENNReal.ofReal (v₀ y))
      hv₀.ennreal_ofReal (h311 θ hθ)
  have hB : ∀ x ∈ M.C, Integrable (ftilde M θ) (greenMeasure M θ x) := fun x hx =>
    ⟨(ftilde_sm M θ).aestronglyMeasurable, (hA x hx).trans_lt ENNReal.ofReal_lt_top⟩
  have hC : ∀ x ∈ M.C, |uStar M θ x| ≤ v₀ x := by
    intro x hx
    rw [← enorm_le_ofReal_iff_abs _ _ (hv₀_nn x hx)]
    exact (enorm_integral_le_lintegral_enorm _).trans (hA x hx)
  have hD : ∀ x ∈ M.C, IntegrableOn (uStar M θ) M.C (discKernel M θ x) := by
    intro x hx
    refine ⟨(uStar_sm M θ).aestronglyMeasurable, ?_⟩
    have h1 : ∫⁻ y in M.C, ‖uStar M θ y‖ₑ ∂(discKernel M θ x)
        ≤ ∫⁻ y in M.C, ENNReal.ofReal (v₀ y) ∂(discKernel M θ x) := by
      apply setLIntegral_mono' M.C_meas
      intro y hy
      exact (enorm_le_ofReal_iff_abs _ _ (hv₀_nn y hy)).2 (hC y hy)
    have h2 := h311 θ hθ x hx
    exact (h1.trans (le_self_add.trans h2)).trans_lt ENNReal.ofReal_lt_top
  intro x hx
  refine ⟨hA x hx, hB x hx, hC x hx, hD x hx, ?_⟩
  rw [uStar, green_integral_first_step M θ (ftilde M θ) (ftilde_sm M θ) x (hB x hx)]
  rfl

end LyapDiffMC.RandomHorizon.Aux

open LyapDiffMC.RandomHorizon in
theorem solution {S : Type*} [MeasurableSpace S] (M : Setting S)
    (θ₀ ε : ℝ) (hε : 0 < ε)
    (hf_int : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      IntegrableOn M.f M.Cᶜ (discKernel M θ x))
    (v₀ : S → ℝ) (hv₀ : Measurable v₀) (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x)
    (h311 : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₀ y) ∂(discKernel M θ x) + ‖ftilde M θ x‖ₑ
        ≤ ENNReal.ofReal (v₀ x)) :
    ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y, ‖ftilde M θ y‖ₑ ∂(greenMeasure M θ x) ≤ ENNReal.ofReal (v₀ x) ∧
      Integrable (ftilde M θ) (greenMeasure M θ x) ∧
      |uStar M θ x| ≤ v₀ x ∧
      IntegrableOn (uStar M θ) M.C (discKernel M θ x) ∧
      uStar M θ x = ftilde M θ x + ∫ y in M.C, uStar M θ y ∂(discKernel M θ x) :=
  LyapDiffMC.RandomHorizon.Aux.bound_main M θ₀ ε v₀ hv₀ hv₀_nn h311
