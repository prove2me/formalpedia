-- Prove2me | solution 1 for LyapDiffMC.RandomHorizon.proof_3_1_continuity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:13:02.531812+00:00
-- url     : https://prove2.me/submissions/e7275529-2802-4765-aff1-6aef7f834c79

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory Filter Topology
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


namespace LyapDiffMC.RandomHorizon.Aux

open LyapDiffMC.RandomHorizon

variable {S : Type*} [MeasurableSpace S]

/-- Mean value bound for the density: `|k(θ, x, y) - k(θ', x, y)| ≤ |θ - θ'| ω_ε(x, y)`. -/
lemma k_lip (k : ℝ → S → S → ℝ) (θ₀ ε : ℝ) (x y : S)
    (hk : ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)))
    (θ θ' : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (hθ' : θ' ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) :
    ‖k θ x y - k θ' x y‖ₑ ≤ ENNReal.ofReal |θ - θ'| * omega k θ₀ ε x y := by
  by_cases hω : omega k θ₀ ε x y = ⊤
  · by_cases hh : θ = θ'
    · subst hh; simp
    · rw [hω, ENNReal.mul_top]
      · exact le_top
      · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, abs_pos]
        exact sub_ne_zero.mpr hh
  · set W := (omega k θ₀ ε x y).toReal
    have hder : ∀ t ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε),
        HasDerivWithinAt (fun θ => k θ x y) (kder k θ₀ ε t x y) (Set.Ioo (θ₀ - ε) (θ₀ + ε)) t := by
      intro t ht
      have hd : DifferentiableAt ℝ (fun θ => k θ x y) t :=
        ((hk.differentiableOn (by norm_num)) t (Set.Ioo_subset_Icc_self ht)).differentiableAt
          (Icc_mem_nhds ht.1 ht.2)
      have : kder k θ₀ ε t x y = deriv (fun θ => k θ x y) t := by
        rw [kder, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      rw [this]
      exact hd.hasDerivAt.hasDerivWithinAt
    have hbd : ∀ t ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ‖kder k θ₀ ε t x y‖ ≤ W := by
      intro t ht
      have h1 : ‖kder k θ₀ ε t x y‖ₑ ≤ omega k θ₀ ε x y := by
        unfold omega
        exact le_iSup₂ (f := fun θ (_ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) =>
          ‖kder k θ₀ ε θ x y‖ₑ) t ht
      rw [← toReal_enorm]
      exact ENNReal.toReal_mono hω h1
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_Ioo _ _) hθ' hθ
    rw [← ofReal_norm_eq_enorm]
    calc ENNReal.ofReal ‖k θ x y - k θ' x y‖ ≤ ENNReal.ofReal (W * ‖θ - θ'‖) :=
          ENNReal.ofReal_le_ofReal this
      _ = ENNReal.ofReal |θ - θ'| * omega k θ₀ ε x y := by
          rw [Real.norm_eq_abs, mul_comm, ENNReal.ofReal_mul (abs_nonneg _),
            ENNReal.ofReal_toReal hω]

section density

variable (M : Setting S) (a b θ₀ : ℝ) (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Ioo a b, Measurable (Function.uncurry (k θ)))
    (hA13 : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C,
      discKernel M θ x = (discKernel M θ₀ x).withDensity (fun y => ENNReal.ofReal (k θ x y)))
    (hk_nonneg : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C, ∀ᵐ y ∂(discKernel M θ₀ x), 0 ≤ k θ x y)

include hk_meas in
lemma k_meas_slice (θ : ℝ) (hθ : θ ∈ Set.Ioo a b) (y : S) : Measurable (fun z => k θ y z) :=
  (hk_meas θ hθ).comp measurable_prodMk_left

include hk_meas hA13 hk_nonneg in
lemma dens_integral (θ : ℝ) (hθ : θ ∈ Set.Ioo a b) (y : S) (hy : y ∈ M.C)
    (s : Set S) (hs : MeasurableSet s) (φ : S → ℝ) :
    ∫ z in s, φ z ∂(discKernel M θ y) = ∫ z in s, k θ y z * φ z ∂(discKernel M θ₀ y) := by
  rw [hA13 θ hθ y hy, setIntegral_withDensity_eq_setIntegral_toReal_smul
    (k_meas_slice a b k hk_meas θ hθ y).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)
    φ hs]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (hk_nonneg θ hθ y hy)] with z hz
  rw [ENNReal.toReal_ofReal hz, smul_eq_mul]

include hk_meas hA13 hk_nonneg in
lemma dens_integrable (θ : ℝ) (hθ : θ ∈ Set.Ioo a b) (y : S) (hy : y ∈ M.C)
    (s : Set S) (hs : MeasurableSet s) (φ : S → ℝ) (hφ : IntegrableOn φ s (discKernel M θ y)) :
    IntegrableOn (fun z => k θ y z * φ z) s (discKernel M θ₀ y) := by
  rw [IntegrableOn, hA13 θ hθ y hy, restrict_withDensity hs,
    integrable_withDensity_iff_integrable_smul'
      (k_meas_slice a b k hk_meas θ hθ y).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hφ
  refine hφ.congr ?_
  filter_upwards [ae_restrict_of_ae (hk_nonneg θ hθ y hy)] with z hz
  rw [ENNReal.toReal_ofReal hz, smul_eq_mul]

include hk_meas hA13 in
lemma dens_lintegral (θ : ℝ) (hθ : θ ∈ Set.Ioo a b) (y : S) (hy : y ∈ M.C)
    (s : Set S) (hs : MeasurableSet s) (F : S → ℝ≥0∞) :
    ∫⁻ z in s, F z ∂(discKernel M θ y)
      = ∫⁻ z in s, ENNReal.ofReal (k θ y z) * F z ∂(discKernel M θ₀ y) := by
  rw [hA13 θ hθ y hy, restrict_withDensity hs,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (k_meas_slice a b k hk_meas θ hθ y).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rfl

end density

lemma diff_bound (M : Setting S) (a b θ₀ ε : ℝ) (hθ₀ : θ₀ ∈ Set.Ioo a b) (hε : 0 < ε)
    (hεΛ : Set.Icc (θ₀ - ε) (θ₀ + ε) ⊆ Set.Ioo a b)
    (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Ioo a b, Measurable (Function.uncurry (k θ)))
    (hA13 : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C,
      discKernel M θ x = (discKernel M θ₀ x).withDensity (fun y => ENNReal.ofReal (k θ x y)))
    (hk_nonneg : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C, ∀ᵐ y ∂(discKernel M θ₀ x), 0 ≤ k θ x y)
    (hA2 : ∀ x ∈ M.C, ∀ y, ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)))
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (y : S) (hy : y ∈ M.C)
    (s : Set S) (hs : MeasurableSet s) (φ : S → ℝ)
    (h1 : IntegrableOn φ s (discKernel M θ y)) (h2 : IntegrableOn φ s (discKernel M θ₀ y)) :
    ‖(∫ z in s, φ z ∂(discKernel M θ y)) - ∫ z in s, φ z ∂(discKernel M θ₀ y)‖ₑ
      ≤ ENNReal.ofReal |θ - θ₀| * ∫⁻ z in s, omega k θ₀ ε y z * ‖φ z‖ₑ ∂(discKernel M θ₀ y) := by
  have hθΛ : θ ∈ Set.Ioo a b := hεΛ (Set.Ioo_subset_Icc_self hθ)
  have hθ₀' : θ₀ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε) := ⟨by linarith, by linarith⟩
  rw [dens_integral M a b θ₀ k hk_meas hA13 hk_nonneg θ hθΛ y hy s hs φ,
    dens_integral M a b θ₀ k hk_meas hA13 hk_nonneg θ₀ hθ₀ y hy s hs φ,
    ← integral_sub (dens_integrable M a b θ₀ k hk_meas hA13 hk_nonneg θ hθΛ y hy s hs φ h1)
      (dens_integrable M a b θ₀ k hk_meas hA13 hk_nonneg θ₀ hθ₀ y hy s hs φ h2)]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hs fun z _ => ?_
  rw [← sub_mul, enorm_mul, ← mul_assoc]
  gcongr
  exact k_lip k θ₀ ε y z (hA2 y hy z) θ θ₀ hθ hθ₀'

lemma diff_bound_raw (M : Setting S) (a b θ₀ : ℝ) (hθ₀ : θ₀ ∈ Set.Ioo a b)
    (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Ioo a b, Measurable (Function.uncurry (k θ)))
    (hA13 : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C,
      discKernel M θ x = (discKernel M θ₀ x).withDensity (fun y => ENNReal.ofReal (k θ x y)))
    (hk_nonneg : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C, ∀ᵐ y ∂(discKernel M θ₀ x), 0 ≤ k θ x y)
    (θ : ℝ) (hθΛ : θ ∈ Set.Ioo a b) (y : S) (hy : y ∈ M.C)
    (s : Set S) (hs : MeasurableSet s) (φ : S → ℝ)
    (h1 : IntegrableOn φ s (discKernel M θ y)) (h2 : IntegrableOn φ s (discKernel M θ₀ y)) :
    ‖(∫ z in s, φ z ∂(discKernel M θ y)) - ∫ z in s, φ z ∂(discKernel M θ₀ y)‖ₑ
      ≤ ∫⁻ z in s, ‖k θ y z - k θ₀ y z‖ₑ * ‖φ z‖ₑ ∂(discKernel M θ₀ y) := by
  rw [dens_integral M a b θ₀ k hk_meas hA13 hk_nonneg θ hθΛ y hy s hs φ,
    dens_integral M a b θ₀ k hk_meas hA13 hk_nonneg θ₀ hθ₀ y hy s hs φ,
    ← integral_sub (dens_integrable M a b θ₀ k hk_meas hA13 hk_nonneg θ hθΛ y hy s hs φ h1)
      (dens_integrable M a b θ₀ k hk_meas hA13 hk_nonneg θ₀ hθ₀ y hy s hs φ h2)]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1; funext z
  rw [← sub_mul, enorm_mul]

lemma uStar_intOn (M : Setting S) (θ₀ ε : ℝ)
    (v₀ : S → ℝ) (hv₀ : Measurable v₀) (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x)
    (h311 : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₀ y) ∂(discKernel M θ x) + ‖ftilde M θ x‖ₑ
        ≤ ENNReal.ofReal (v₀ x))
    (θ θ' : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (hθ' : θ' ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε))
    (y : S) (hy : y ∈ M.C) :
    IntegrableOn (uStar M θ) M.C (discKernel M θ' y) := by
  have bnd := bound_main M θ₀ ε v₀ hv₀ hv₀_nn h311
  refine ⟨(uStar_sm M θ).aestronglyMeasurable, ?_⟩
  have h1 : ∫⁻ z in M.C, ‖uStar M θ z‖ₑ ∂(discKernel M θ' y)
      ≤ ∫⁻ z in M.C, ENNReal.ofReal (v₀ z) ∂(discKernel M θ' y) := by
    apply setLIntegral_mono' M.C_meas
    intro z hz
    exact (enorm_le_ofReal_iff_abs _ _ (hv₀_nn z hz)).2 (bnd θ hθ z hz).2.2.1
  exact (h1.trans (le_self_add.trans (h311 θ' hθ' y hy))).trans_lt ENNReal.ofReal_lt_top

lemma intOn_of_abs_le (M : Setting S) (μ : Measure S) (φ v : S → ℝ) (hφ : AEStronglyMeasurable φ (μ.restrict M.C))
    (hv : ∀ z ∈ M.C, |φ z| ≤ v z)
    (hfin : ∫⁻ z in M.C, ENNReal.ofReal (v z) ∂μ < ⊤) : IntegrableOn φ M.C μ := by
  refine ⟨hφ, ?_⟩
  have h1 : ∫⁻ z in M.C, ‖φ z‖ₑ ∂μ ≤ ∫⁻ z in M.C, ENNReal.ofReal (v z) ∂μ := by
    apply setLIntegral_mono' M.C_meas
    intro z hz
    exact (enorm_le_ofReal_iff_abs _ _ ((abs_nonneg _).trans (hv z hz))).2 (hv z hz)
  exact h1.trans_lt hfin

/-- `|(K(θ) - K)φ| ≤ |θ - θ₀| ∫_C ω_ε v₀ dK` for `|φ| ≤ v₀` on `C`. -/
lemma diff_bound_v₀ (M : Setting S) (a b θ₀ ε : ℝ) (hθ₀ : θ₀ ∈ Set.Ioo a b) (hε : 0 < ε)
    (hεΛ : Set.Icc (θ₀ - ε) (θ₀ + ε) ⊆ Set.Ioo a b)
    (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Ioo a b, Measurable (Function.uncurry (k θ)))
    (hA13 : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C,
      discKernel M θ x = (discKernel M θ₀ x).withDensity (fun y => ENNReal.ofReal (k θ x y)))
    (hk_nonneg : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C, ∀ᵐ y ∂(discKernel M θ₀ x), 0 ≤ k θ x y)
    (hA2 : ∀ x ∈ M.C, ∀ y, ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)))
    (v₀ : S → ℝ) (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x)
    (h311 : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₀ y) ∂(discKernel M θ x) + ‖ftilde M θ x‖ₑ
        ≤ ENNReal.ofReal (v₀ x))
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (y : S) (hy : y ∈ M.C)
    (φ : S → ℝ) (hφm : StronglyMeasurable φ) (hφ : ∀ z ∈ M.C, |φ z| ≤ v₀ z) :
    IntegrableOn φ M.C (discKernel M θ y) ∧ IntegrableOn φ M.C (discKernel M θ₀ y) ∧
    ‖(∫ z in M.C, φ z ∂(discKernel M θ y)) - ∫ z in M.C, φ z ∂(discKernel M θ₀ y)‖ₑ
      ≤ ENNReal.ofReal |θ - θ₀| *
        ∫⁻ z in M.C, omega k θ₀ ε y z * ENNReal.ofReal (v₀ z) ∂(discKernel M θ₀ y) := by
  have hθ₀' : θ₀ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε) := ⟨by linarith, by linarith⟩
  have i1 : IntegrableOn φ M.C (discKernel M θ y) :=
    intOn_of_abs_le M _ φ v₀ hφm.aestronglyMeasurable hφ
      ((le_self_add.trans (h311 θ hθ y hy)).trans_lt ENNReal.ofReal_lt_top)
  have i2 : IntegrableOn φ M.C (discKernel M θ₀ y) :=
    intOn_of_abs_le M _ φ v₀ hφm.aestronglyMeasurable hφ
      ((le_self_add.trans (h311 θ₀ hθ₀' y hy)).trans_lt ENNReal.ofReal_lt_top)
  refine ⟨i1, i2, ?_⟩
  refine (diff_bound M a b θ₀ ε hθ₀ hε hεΛ k hk_meas hA13 hk_nonneg hA2 θ hθ y hy M.C M.C_meas
    φ i1 i2).trans ?_
  refine mul_le_mul_right (setLIntegral_mono' M.C_meas fun z hz => ?_) _
  exact mul_le_mul_right ((enorm_le_ofReal_iff_abs _ _ (hv₀_nn z hz)).2 (hφ z hz)) _

/-- `|f̃(θ) - f̃(θ₀)| ≤ |θ - θ₀| r̃_ε`. -/
lemma ftilde_diff_bound (M : Setting S) (a b θ₀ ε : ℝ) (hθ₀ : θ₀ ∈ Set.Ioo a b) (hε : 0 < ε)
    (hεΛ : Set.Icc (θ₀ - ε) (θ₀ + ε) ⊆ Set.Ioo a b)
    (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Ioo a b, Measurable (Function.uncurry (k θ)))
    (hA13 : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C,
      discKernel M θ x = (discKernel M θ₀ x).withDensity (fun y => ENNReal.ofReal (k θ x y)))
    (hk_nonneg : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C, ∀ᵐ y ∂(discKernel M θ₀ x), 0 ≤ k θ x y)
    (hA2 : ∀ x ∈ M.C, ∀ y, ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)))
    (hf_int : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      IntegrableOn M.f M.Cᶜ (discKernel M θ x))
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (y : S) (hy : y ∈ M.C) :
    ‖ftilde M θ y - ftilde M θ₀ y‖ₑ ≤ ENNReal.ofReal |θ - θ₀| * rtilde M k θ₀ ε y := by
  have hθ₀' : θ₀ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε) := ⟨by linarith, by linarith⟩
  have e : ftilde M θ y - ftilde M θ₀ y
      = (∫ z in M.Cᶜ, M.f z ∂(discKernel M θ y)) - ∫ z in M.Cᶜ, M.f z ∂(discKernel M θ₀ y) := by
    simp only [ftilde]; ring
  rw [e]
  exact diff_bound M a b θ₀ ε hθ₀ hε hεΛ k hk_meas hA13 hk_nonneg hA2 θ hθ y hy M.Cᶜ
    M.C_meas.compl M.f (hf_int θ hθ y hy) (hf_int θ₀ hθ₀' y hy)

lemma kint_sm (M : Setting S) (θ : ℝ) (s : Set S) (hs : MeasurableSet s) (φ : S → ℝ)
    (hφ : StronglyMeasurable φ) :
    StronglyMeasurable (fun y => ∫ z in s, φ z ∂(discKernel M θ y)) := by
  have h1 : StronglyMeasurable fun y => ∫ z, φ z ∂((discKernel M θ).restrict hs y) :=
    StronglyMeasurable.integral_kernel_prod_right'
      (f := fun p : S × S => φ p.2) (hφ.comp_measurable measurable_snd)
  have h2 : (fun y => ∫ z, φ z ∂((discKernel M θ).restrict hs y))
      = fun y => ∫ z in s, φ z ∂(discKernel M θ y) := by
    funext y; rw [Kernel.restrict_apply]
  rwa [h2] at h1

lemma kpow_le_green (M : Setting S) (θ : ℝ) (n : ℕ) (x : S) :
    kpow M θ n x ≤ greenMeasure M θ x := Measure.le_sum (fun n => kpow M θ n x) n

lemma kpow_conc (M : Setting S) (θ : ℝ) (n : ℕ) (x : S) (hx : x ∈ M.C) :
    ∀ᵐ y ∂(kpow M θ n x), y ∈ M.C := by
  rw [ae_iff]; exact Qpow_conc (KC M θ) M.C M.C_meas (KC_compl M θ) n x hx

lemma kpow_succ_apply (M : Setting S) (θ : ℝ) (n : ℕ) (x : S) :
    kpow M θ (n + 1) x = (kpow M θ n ∘ₖ KC M θ) x := by
  rw [kpow, Qpow_succ']; rfl

lemma kpow_zero_apply (M : Setting S) (θ : ℝ) (x : S) :
    kpow M θ 0 x = Measure.dirac x := by
  rw [kpow, Qpow, Kernel.id_apply]

/-- First-step decomposition of a `Kⁿ⁺¹(θ, x, ·)`-integral. -/
lemma kpow_succ_integral (M : Setting S) (θ : ℝ) (n : ℕ) (x : S) (F : S → ℝ)
    (hF : Integrable F (kpow M θ (n + 1) x)) :
    Integrable (fun y => ∫ z, F z ∂(kpow M θ n y)) ((discKernel M θ x).restrict M.C) ∧
    ∫ z, F z ∂(kpow M θ (n + 1) x)
      = ∫ y in M.C, (∫ z, F z ∂(kpow M θ n y)) ∂(discKernel M θ x) := by
  rw [kpow_succ_apply] at hF ⊢
  refine ⟨?_, ?_⟩
  · have := hF.integral_comp
    rwa [KC_apply] at this
  · rw [Kernel.integral_comp hF, KC_apply]

/-- Truncated potential `T_N(θ, x) = Σ_{m<N} (K^m(θ) f̃(θ))(x)`. -/
noncomputable def Tr (M : Setting S) (θ : ℝ) (N : ℕ) (x : S) : ℝ :=
  ∑ m ∈ Finset.range N, ∫ y, ftilde M θ y ∂(kpow M θ m x)

lemma Tr_sm (M : Setting S) (θ : ℝ) (N : ℕ) : StronglyMeasurable (Tr M θ N) := by
  have : ∀ m, StronglyMeasurable fun x => ∫ y, ftilde M θ y ∂(kpow M θ m x) := fun m =>
    StronglyMeasurable.integral_kernel_prod_right'
      (f := fun p : S × S => ftilde M θ p.2) ((ftilde_sm M θ).comp_measurable measurable_snd)
  unfold Tr
  exact Finset.stronglyMeasurable_fun_sum _ fun m _ => this m

lemma Tr_enorm_le (M : Setting S) (θ : ℝ) (N : ℕ) (x : S) :
    ‖Tr M θ N x‖ₑ ≤ ∫⁻ y, ‖ftilde M θ y‖ₑ ∂(greenMeasure M θ x) := by
  unfold Tr
  refine (enorm_sum_le _ _).trans ?_
  rw [greenMeasure, lintegral_sum_measure]
  refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.range N))
  exact Finset.sum_le_sum fun m _ => enorm_integral_le_lintegral_enorm _

lemma Tr_tendsto (M : Setting S) (θ : ℝ) (x : S)
    (hint : Integrable (ftilde M θ) (greenMeasure M θ x)) :
    Tendsto (fun N => Tr M θ N x) atTop (𝓝 (uStar M θ x)) := by
  have := (hasSum_integral_measure (μ := fun n => kpow M θ n x) hint)
  exact this.tendsto_sum_nat

lemma Tr_succ (M : Setting S) (θ : ℝ) (N : ℕ) (x : S)
    (hint : Integrable (ftilde M θ) (greenMeasure M θ x)) :
    Tr M θ (N + 1) x = ftilde M θ x + ∫ y in M.C, Tr M θ N y ∂(discKernel M θ x) := by
  unfold Tr
  rw [Finset.sum_range_succ', kpow_zero_apply, integral_dirac' _ _ (ftilde_sm M θ), add_comm]
  congr 1
  have h : ∀ m, Integrable (ftilde M θ) (kpow M θ (m + 1) x) := fun m =>
    hint.mono_measure (kpow_le_green M θ (m + 1) x)
  rw [integral_finset_sum _ fun m _ => (kpow_succ_integral M θ m x _ (h m)).1]
  exact Finset.sum_congr rfl fun m _ => (kpow_succ_integral M θ m x _ (h m)).2

/-- The hypotheses of Theorem 3.1 (I), bundled. -/
structure Hyp (M : Setting S) (a b θ₀ ε : ℝ) (k : ℝ → S → S → ℝ) (v₀ v₁ : S → ℝ) : Prop where
  hθ₀ : θ₀ ∈ Set.Ioo a b
  hε : 0 < ε
  hεΛ : Set.Icc (θ₀ - ε) (θ₀ + ε) ⊆ Set.Ioo a b
  hk_meas : ∀ θ ∈ Set.Ioo a b, Measurable (Function.uncurry (k θ))
  hA13 : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C,
      discKernel M θ x = (discKernel M θ₀ x).withDensity (fun y => ENNReal.ofReal (k θ x y))
  hk_nonneg : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C, ∀ᵐ y ∂(discKernel M θ₀ x), 0 ≤ k θ x y
  hA2 : ∀ x ∈ M.C, ∀ y, ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε))
  hA3 : ∀ x ∈ M.C, rtilde M k θ₀ ε x < ⊤
  hf_int : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      IntegrableOn M.f M.Cᶜ (discKernel M θ x)
  hv₀ : Measurable v₀
  hv₁ : Measurable v₁
  hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x
  hv₁_nn : ∀ x ∈ M.C, 0 ≤ v₁ x
  h311 : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₀ y) ∂(discKernel M θ x) + ‖ftilde M θ x‖ₑ
        ≤ ENNReal.ofReal (v₀ x)
  h312 : ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₁ y) ∂(discKernel M θ₀ x)
        + ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₀ y) ∂(discKernel M θ₀ x)
        + rtilde M k θ₀ ε x ≤ ENNReal.ofReal (v₁ x)

namespace Hyp

variable {M : Setting S} {a b θ₀ ε : ℝ} {k : ℝ → S → S → ℝ} {v₀ v₁ : S → ℝ}
  (H : Hyp M a b θ₀ ε k v₀ v₁)
include H

lemma θ₀_mem : θ₀ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε) := ⟨by linarith [H.hε], by linarith [H.hε]⟩

lemma mem_Λ {θ : ℝ} (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) : θ ∈ Set.Ioo a b :=
  H.hεΛ (Set.Ioo_subset_Icc_self hθ)

/-- The weight `A(y) + r̃(y)` with `A(y) = ∫_C ω_ε(y, z) v₀(z) K(y, dz)`. -/
noncomputable def W (_H : Hyp M a b θ₀ ε k v₀ v₁) (y : S) : ℝ≥0∞ :=
  ∫⁻ z in M.C, omega k θ₀ ε y z * ENNReal.ofReal (v₀ z) ∂(discKernel M θ₀ y) + rtilde M k θ₀ ε y

lemma green_W (x : S) (hx : x ∈ M.C) :
    ∫⁻ y, H.W y ∂(greenMeasure M θ₀ x) ≤ ENNReal.ofReal (v₁ x) := by
  refine green_bound M θ₀ H.W (fun y => ENNReal.ofReal (v₁ y)) H.hv₁.ennreal_ofReal ?_ x hx
  intro y hy
  have := H.h312 y hy
  simp only [W]
  rw [← add_assoc]; exact this

/-- `|(K(θ) - K)φ| ≤ |θ - θ₀| A` for `|φ| ≤ v₀` on `C`. -/
lemma Kdiff (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (y : S) (hy : y ∈ M.C)
    (φ : S → ℝ) (hφm : StronglyMeasurable φ) (hφ : ∀ z ∈ M.C, |φ z| ≤ v₀ z) :
    IntegrableOn φ M.C (discKernel M θ y) ∧ IntegrableOn φ M.C (discKernel M θ₀ y) ∧
    ‖(∫ z in M.C, φ z ∂(discKernel M θ y)) - ∫ z in M.C, φ z ∂(discKernel M θ₀ y)‖ₑ
      ≤ ENNReal.ofReal |θ - θ₀| *
        ∫⁻ z in M.C, omega k θ₀ ε y z * ENNReal.ofReal (v₀ z) ∂(discKernel M θ₀ y) :=
  diff_bound_v₀ M a b θ₀ ε H.hθ₀ H.hε H.hεΛ k H.hk_meas H.hA13 H.hk_nonneg H.hA2 v₀ H.hv₀_nn
    H.h311 θ hθ y hy φ hφm hφ

lemma fdiff (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (y : S) (hy : y ∈ M.C) :
    ‖ftilde M θ y - ftilde M θ₀ y‖ₑ ≤ ENNReal.ofReal |θ - θ₀| * rtilde M k θ₀ ε y :=
  ftilde_diff_bound M a b θ₀ ε H.hθ₀ H.hε H.hεΛ k H.hk_meas H.hA13 H.hk_nonneg H.hA2 H.hf_int
    θ hθ y hy

lemma bnd (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (x : S) (hx : x ∈ M.C) :
      ∫⁻ y, ‖ftilde M θ y‖ₑ ∂(greenMeasure M θ x) ≤ ENNReal.ofReal (v₀ x) ∧
      Integrable (ftilde M θ) (greenMeasure M θ x) ∧
      |uStar M θ x| ≤ v₀ x ∧
      IntegrableOn (uStar M θ) M.C (discKernel M θ x) ∧
      uStar M θ x = ftilde M θ x + ∫ y in M.C, uStar M θ y ∂(discKernel M θ x) :=
  bound_main M θ₀ ε v₀ H.hv₀ H.hv₀_nn H.h311 θ hθ x hx

/-- The perturbation `R_θ(y) = (K(θ) - K)u*(θ)(y) + f̃(θ, y) - f̃(θ₀, y)`, split in two. -/
lemma lip_pointwise (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (y : S) (hy : y ∈ M.C) :
    ‖(∫ z in M.C, uStar M θ z ∂(discKernel M θ y))
              - ∫ z in M.C, uStar M θ z ∂(discKernel M θ₀ y)‖ₑ
            + ‖ftilde M θ y - ftilde M θ₀ y‖ₑ ≤ ENNReal.ofReal |θ - θ₀| * H.W y := by
  rw [W, mul_add]
  gcongr
  · exact (H.Kdiff θ hθ y hy (uStar M θ) (uStar_sm M θ)
      (fun z hz => (H.bnd θ hθ z hz).2.2.1)).2.2
  · exact H.fdiff θ hθ y hy

lemma lip_integral (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (x : S) (hx : x ∈ M.C) :
    ∫⁻ y, (‖(∫ z in M.C, uStar M θ z ∂(discKernel M θ y))
              - ∫ z in M.C, uStar M θ z ∂(discKernel M θ₀ y)‖ₑ
            + ‖ftilde M θ y - ftilde M θ₀ y‖ₑ) ∂(greenMeasure M θ₀ x)
        ≤ ENNReal.ofReal (|θ - θ₀| * v₁ x) := by
  calc _ ≤ ∫⁻ y, ENNReal.ofReal |θ - θ₀| * H.W y ∂(greenMeasure M θ₀ x) := by
        apply lintegral_mono_ae
        filter_upwards [ae_green_mem M θ₀ x hx] with y hy
        exact H.lip_pointwise θ hθ y hy
    _ = ENNReal.ofReal |θ - θ₀| * ∫⁻ y, H.W y ∂(greenMeasure M θ₀ x) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal |θ - θ₀| * ENNReal.ofReal (v₁ x) := by gcongr; exact H.green_W x hx
    _ = ENNReal.ofReal (|θ - θ₀| * v₁ x) := (ENNReal.ofReal_mul (abs_nonneg _)).symm

/-- A measurable majorant of the perturbation `|R_θ|`. -/
noncomputable def Bm (_H : Hyp M a b θ₀ ε k v₀ v₁) (θ : ℝ) (y : S) : ℝ≥0∞ :=
  ∫⁻ z in M.C, ‖k θ y z - k θ₀ y z‖ₑ * ENNReal.ofReal (v₀ z) ∂(discKernel M θ₀ y)
    + ∫⁻ z in M.Cᶜ, ‖k θ y z - k θ₀ y z‖ₑ * ‖M.f z‖ₑ ∂(discKernel M θ₀ y)

lemma Bm_meas (θ : ℝ) (hθ : θ ∈ Set.Ioo a b) : Measurable (H.Bm θ) := by
  have hk : Measurable fun p : S × S => ‖k θ p.1 p.2 - k θ₀ p.1 p.2‖ₑ :=
    ((H.hk_meas θ hθ).sub (H.hk_meas θ₀ H.hθ₀)).enorm
  have m1 : Measurable fun y =>
      ∫⁻ z, ‖k θ y z - k θ₀ y z‖ₑ * ENNReal.ofReal (v₀ z) ∂((discKernel M θ₀).restrict M.C_meas y) :=
    Measurable.lintegral_kernel_prod_right'
      (f := fun p : S × S => ‖k θ p.1 p.2 - k θ₀ p.1 p.2‖ₑ * ENNReal.ofReal (v₀ p.2))
      (hk.mul (H.hv₀.comp measurable_snd).ennreal_ofReal)
  have m2 : Measurable fun y =>
      ∫⁻ z, ‖k θ y z - k θ₀ y z‖ₑ * ‖M.f z‖ₑ ∂((discKernel M θ₀).restrict M.C_meas.compl y) :=
    Measurable.lintegral_kernel_prod_right'
      (f := fun p : S × S => ‖k θ p.1 p.2 - k θ₀ p.1 p.2‖ₑ * ‖M.f p.2‖ₑ)
      (hk.mul (M.f_meas.comp measurable_snd).enorm)
  simp only [Kernel.restrict_apply] at m1 m2
  exact m1.add m2

lemma Bm_le (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (y : S) (hy : y ∈ M.C) :
    H.Bm θ y ≤ ENNReal.ofReal |θ - θ₀| * H.W y := by
  rw [Bm, W, mul_add, rtilde, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine add_le_add (lintegral_mono fun z => ?_) (lintegral_mono fun z => ?_)
  · rw [← mul_assoc]; exact mul_le_mul' (k_lip k θ₀ ε y z (H.hA2 y hy z) θ θ₀ hθ H.θ₀_mem) le_rfl
  · rw [← mul_assoc]; exact mul_le_mul' (k_lip k θ₀ ε y z (H.hA2 y hy z) θ θ₀ hθ H.θ₀_mem) le_rfl

lemma green_Bm (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (x : S) (hx : x ∈ M.C) :
    ∫⁻ y, H.Bm θ y ∂(greenMeasure M θ₀ x) ≤ ENNReal.ofReal (|θ - θ₀| * v₁ x) := by
  calc _ ≤ ∫⁻ y, ENNReal.ofReal |θ - θ₀| * H.W y ∂(greenMeasure M θ₀ x) := by
        apply lintegral_mono_ae
        filter_upwards [ae_green_mem M θ₀ x hx] with y hy
        exact H.Bm_le θ hθ y hy
    _ = ENNReal.ofReal |θ - θ₀| * ∫⁻ y, H.W y ∂(greenMeasure M θ₀ x) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal |θ - θ₀| * ENNReal.ofReal (v₁ x) := by gcongr; exact H.green_W x hx
    _ = ENNReal.ofReal (|θ - θ₀| * v₁ x) := (ENNReal.ofReal_mul (abs_nonneg _)).symm

/-- `R_θ[φ](y) = (K(θ) - K)φ(y) + f̃(θ, y) - f̃(θ₀, y)`. -/
noncomputable def Rf (_H : Hyp M a b θ₀ ε k v₀ v₁) (θ : ℝ) (φ : S → ℝ) (y : S) : ℝ :=
  ((∫ z in M.C, φ z ∂(discKernel M θ y)) - ∫ z in M.C, φ z ∂(discKernel M θ₀ y))
    + (ftilde M θ y - ftilde M θ₀ y)

lemma Rf_sm (θ : ℝ) (φ : S → ℝ) (hφ : StronglyMeasurable φ) : StronglyMeasurable (H.Rf θ φ) :=
  ((kint_sm M θ M.C M.C_meas φ hφ).sub (kint_sm M θ₀ M.C M.C_meas φ hφ)).add
    ((ftilde_sm M θ).sub (ftilde_sm M θ₀))

lemma Rf_le (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (φ : S → ℝ) (hφm : StronglyMeasurable φ)
    (hφ : ∀ z ∈ M.C, |φ z| ≤ v₀ z) (y : S) (hy : y ∈ M.C) :
    ‖H.Rf θ φ y‖ₑ ≤ H.Bm θ y := by
  have hθΛ := H.mem_Λ hθ
  have hK := H.Kdiff θ hθ y hy φ hφm hφ
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (diff_bound_raw M a b θ₀ H.hθ₀ k H.hk_meas H.hA13 H.hk_nonneg θ hθΛ y hy M.C M.C_meas
      φ hK.1 hK.2.1).trans ?_
    refine setLIntegral_mono' M.C_meas fun z hz => ?_
    gcongr
    exact (enorm_le_ofReal_iff_abs _ _ (H.hv₀_nn z hz)).2 (hφ z hz)
  · have e : ftilde M θ y - ftilde M θ₀ y
        = (∫ z in M.Cᶜ, M.f z ∂(discKernel M θ y)) - ∫ z in M.Cᶜ, M.f z ∂(discKernel M θ₀ y) := by
      simp only [ftilde]; ring
    rw [e]
    exact diff_bound_raw M a b θ₀ H.hθ₀ k H.hk_meas H.hA13 H.hk_nonneg θ hθΛ y hy M.Cᶜ
      M.C_meas.compl M.f (H.hf_int θ hθ y hy) (H.hf_int θ₀ H.θ₀_mem y hy)

lemma Rf_int (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (φ : S → ℝ) (hφm : StronglyMeasurable φ)
    (hφ : ∀ z ∈ M.C, |φ z| ≤ v₀ z) (x : S) (hx : x ∈ M.C) (μ : Measure S)
    (hμ : μ ≤ greenMeasure M θ₀ x) (hc : ∀ᵐ y ∂μ, y ∈ M.C) :
    Integrable (H.Rf θ φ) μ := by
  refine ⟨(H.Rf_sm θ φ hφm).aestronglyMeasurable, ?_⟩
  have h1 : ∫⁻ y, ‖H.Rf θ φ y‖ₑ ∂μ ≤ ∫⁻ y, H.Bm θ y ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [hc] with y hy
    exact H.Rf_le θ hθ φ hφm hφ y hy
  refine (h1.trans ((lintegral_mono' hμ le_rfl).trans (H.green_Bm θ hθ x hx))).trans_lt ?_
  exact ENNReal.ofReal_lt_top

lemma Tr_abs (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (N : ℕ) (y : S) (hy : y ∈ M.C) :
    |Tr M θ N y| ≤ v₀ y :=
  (enorm_le_ofReal_iff_abs _ _ (H.hv₀_nn y hy)).1
    ((Tr_enorm_le M θ N y).trans (H.bnd θ hθ y hy).1)

lemma intOn_v₀bdd (θ' : ℝ) (hθ' : θ' ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (y : S) (hy : y ∈ M.C)
    (φ : S → ℝ) (hφm : StronglyMeasurable φ) (hφ : ∀ z ∈ M.C, |φ z| ≤ v₀ z) :
    IntegrableOn φ M.C (discKernel M θ' y) :=
  intOn_of_abs_le M _ φ v₀ hφm.aestronglyMeasurable hφ
    ((le_self_add.trans (H.h311 θ' hθ' y hy)).trans_lt ENNReal.ofReal_lt_top)

lemma D_rec (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (N : ℕ) (x : S) (hx : x ∈ M.C) :
    Tr M θ (N + 1) x - Tr M θ₀ (N + 1) x
      = H.Rf θ (Tr M θ N) x + ∫ y in M.C, (Tr M θ N y - Tr M θ₀ N y) ∂(discKernel M θ₀ x) := by
  rw [Tr_succ M θ N x (H.bnd θ hθ x hx).2.1, Tr_succ M θ₀ N x (H.bnd θ₀ H.θ₀_mem x hx).2.1,
    integral_sub (H.intOn_v₀bdd θ₀ H.θ₀_mem x hx _ (Tr_sm M θ N) (fun z hz => H.Tr_abs θ hθ N z hz))
      (H.intOn_v₀bdd θ₀ H.θ₀_mem x hx _ (Tr_sm M θ₀ N)
        (fun z hz => H.Tr_abs θ₀ H.θ₀_mem N z hz))]
  simp only [Rf]; ring

lemma Rf_Tr_int (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (M' : ℕ) (j : ℕ) (x : S)
    (hx : x ∈ M.C) : Integrable (H.Rf θ (Tr M θ M')) (kpow M θ₀ j x) :=
  H.Rf_int θ hθ _ (Tr_sm M θ M') (fun z hz => H.Tr_abs θ hθ M' z hz) x hx _
    (kpow_le_green M θ₀ j x) (kpow_conc M θ₀ j x hx)

lemma D_formula (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) :
    ∀ N, ∀ x ∈ M.C, Tr M θ N x - Tr M θ₀ N x
      = ∑ j ∈ Finset.range N, ∫ y, H.Rf θ (Tr M θ (N - 1 - j)) y ∂(kpow M θ₀ j x) := by
  intro N
  induction N with
  | zero => intro x _; simp [Tr]
  | succ N ih =>
    intro x hx
    rw [H.D_rec θ hθ N x hx]
    have e1 : ∫ y in M.C, (Tr M θ N y - Tr M θ₀ N y) ∂(discKernel M θ₀ x)
        = ∫ y in M.C, (∑ j ∈ Finset.range N,
            ∫ z, H.Rf θ (Tr M θ (N - 1 - j)) z ∂(kpow M θ₀ j y)) ∂(discKernel M θ₀ x) := by
      refine setIntegral_congr_fun M.C_meas fun y hy => ?_
      exact ih y hy
    have hint : ∀ j, Integrable (H.Rf θ (Tr M θ (N - 1 - j))) (kpow M θ₀ (j + 1) x) :=
      fun j => H.Rf_Tr_int θ hθ _ _ x hx
    rw [e1, integral_finset_sum _ fun j _ => (kpow_succ_integral M θ₀ j x _ (hint j)).1]
    rw [Finset.sum_range_succ', kpow_zero_apply,
      integral_dirac' _ _ (H.Rf_sm θ _ (Tr_sm M θ _)), add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show N + 1 - 1 - (j + 1) = N - 1 - j by omega]
      exact ((kpow_succ_integral M θ₀ j x _ (hint j)).2).symm

lemma Rf_Tr_tendsto (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (y : S) (hy : y ∈ M.C) :
    Tendsto (fun N => H.Rf θ (Tr M θ N) y) atTop (𝓝 (H.Rf θ (uStar M θ) y)) := by
  have key : ∀ θ' ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε),
      Tendsto (fun N => ∫ z in M.C, Tr M θ N z ∂(discKernel M θ' y)) atTop
        (𝓝 (∫ z in M.C, uStar M θ z ∂(discKernel M θ' y))) := by
    intro θ' hθ'
    refine tendsto_integral_of_dominated_convergence v₀
      (fun N => (Tr_sm M θ N).aestronglyMeasurable)
      (H.intOn_v₀bdd θ' hθ' y hy v₀ H.hv₀.stronglyMeasurable
        (fun z hz => by rw [abs_of_nonneg (H.hv₀_nn z hz)]))
      (fun N => ?_) ?_
    · filter_upwards [ae_restrict_mem M.C_meas] with z hz
      rw [Real.norm_eq_abs]; exact H.Tr_abs θ hθ N z hz
    · filter_upwards [ae_restrict_mem M.C_meas] with z hz
      exact Tr_tendsto M θ z (H.bnd θ hθ z hz).2.1
  exact ((key θ hθ).sub (key θ₀ H.θ₀_mem)).add tendsto_const_nhds

lemma lint_Bm_kpow_lt (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (j : ℕ) (x : S)
    (hx : x ∈ M.C) : ∫⁻ y, H.Bm θ y ∂(kpow M θ₀ j x) ≠ ⊤ :=
  ((lintegral_mono' (kpow_le_green M θ₀ j x) le_rfl).trans_lt
    ((H.green_Bm θ hθ x hx).trans_lt ENNReal.ofReal_lt_top)).ne

lemma norm_int_le_Bm (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (φ : S → ℝ)
    (hφm : StronglyMeasurable φ) (hφ : ∀ z ∈ M.C, |φ z| ≤ v₀ z) (j : ℕ) (x : S) (hx : x ∈ M.C) :
    ‖∫ y, H.Rf θ φ y ∂(kpow M θ₀ j x)‖ ≤ (∫⁻ y, H.Bm θ y ∂(kpow M θ₀ j x)).toReal := by
  rw [← toReal_enorm]
  refine ENNReal.toReal_mono (H.lint_Bm_kpow_lt θ hθ j x hx)
    ((enorm_integral_le_lintegral_enorm _).trans ?_)
  apply lintegral_mono_ae
  filter_upwards [kpow_conc M θ₀ j x hx] with y hy
  exact H.Rf_le θ hθ φ hφm hφ y hy

/-- The key identity behind (3.19): `u*(θ) - u*(θ₀) = G R_θ`, with `R_θ` integrable. -/
lemma identity (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (x : S) (hx : x ∈ M.C) :
    Integrable (H.Rf θ (uStar M θ)) (greenMeasure M θ₀ x) ∧
    uStar M θ x - uStar M θ₀ x = ∫ y, H.Rf θ (uStar M θ) y ∂(greenMeasure M θ₀ x) := by
  have hu : ∀ z ∈ M.C, |uStar M θ z| ≤ v₀ z := fun z hz => (H.bnd θ hθ z hz).2.2.1
  have hRint : Integrable (H.Rf θ (uStar M θ)) (greenMeasure M θ₀ x) :=
    H.Rf_int θ hθ _ (uStar_sm M θ) hu x hx _ le_rfl (ae_green_mem M θ₀ x hx)
  refine ⟨hRint, ?_⟩
  have hL : Tendsto (fun N => Tr M θ N x - Tr M θ₀ N x) atTop
      (𝓝 (uStar M θ x - uStar M θ₀ x)) :=
    (Tr_tendsto M θ x (H.bnd θ hθ x hx).2.1).sub
      (Tr_tendsto M θ₀ x (H.bnd θ₀ H.θ₀_mem x hx).2.1)
  let F : ℕ → ℕ → ℝ := fun N j =>
    if j < N then ∫ y, H.Rf θ (Tr M θ (N - 1 - j)) y ∂(kpow M θ₀ j x) else 0
  have eqF : ∀ N, Tr M θ N x - Tr M θ₀ N x = ∑' j, F N j := by
    intro N
    rw [H.D_formula θ hθ N x hx, tsum_eq_sum (s := Finset.range N)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp only [F, if_pos (Finset.mem_range.mp hj)]
    · intro j hj
      have : ¬ j < N := by simpa using hj
      simp only [F, if_neg this]
  have hR : Tendsto (fun N => ∑' j, F N j) atTop
      (𝓝 (∑' j, ∫ y, H.Rf θ (uStar M θ) y ∂(kpow M θ₀ j x))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun j => (∫⁻ y, H.Bm θ y ∂(kpow M θ₀ j x)).toReal) ?_ ?_ ?_
    · refine ENNReal.summable_toReal ?_
      rw [← lintegral_sum_measure]
      exact ((H.green_Bm θ hθ x hx).trans_lt ENNReal.ofReal_lt_top).ne
    · intro j
      have hdct : Tendsto (fun m => ∫ y, H.Rf θ (Tr M θ m) y ∂(kpow M θ₀ j x)) atTop
          (𝓝 (∫ y, H.Rf θ (uStar M θ) y ∂(kpow M θ₀ j x))) := by
        refine tendsto_integral_of_dominated_convergence (fun y => (H.Bm θ y).toReal)
          (fun m => (H.Rf_sm θ _ (Tr_sm M θ m)).aestronglyMeasurable)
          (integrable_toReal_of_lintegral_ne_top (H.Bm_meas θ (H.mem_Λ hθ)).aemeasurable
            (H.lint_Bm_kpow_lt θ hθ j x hx)) (fun m => ?_) ?_
        · filter_upwards [kpow_conc M θ₀ j x hx,
            ae_lt_top (H.Bm_meas θ (H.mem_Λ hθ)) (H.lint_Bm_kpow_lt θ hθ j x hx)] with y hy hfin
          rw [← toReal_enorm]
          exact ENNReal.toReal_mono hfin.ne
            (H.Rf_le θ hθ _ (Tr_sm M θ m) (fun z hz => H.Tr_abs θ hθ m z hz) y hy)
        · filter_upwards [kpow_conc M θ₀ j x hx] with y hy
          exact H.Rf_Tr_tendsto θ hθ y hy
      have hsub : Tendsto (fun N => N - 1 - j) atTop atTop :=
        (tendsto_sub_atTop_nat j).comp (tendsto_sub_atTop_nat 1)
      refine (hdct.comp hsub).congr' ?_
      filter_upwards [eventually_gt_atTop j] with N hN
      simp only [F, Function.comp, if_pos hN]
    · refine Eventually.of_forall fun N j => ?_
      simp only [F]
      split_ifs
      · exact H.norm_int_le_Bm θ hθ _ (Tr_sm M θ _) (fun z hz => H.Tr_abs θ hθ _ z hz) j x hx
      · simp
  have hR' : Tendsto (fun N => Tr M θ N x - Tr M θ₀ N x) atTop
      (𝓝 (∑' j, ∫ y, H.Rf θ (uStar M θ) y ∂(kpow M θ₀ j x))) := by
    simp_rw [eqF]; exact hR
  rw [tendsto_nhds_unique hL hR', greenMeasure, integral_sum_measure]
  rwa [greenMeasure] at hRint

lemma lip_u (θ : ℝ) (hθ : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε)) (x : S) (hx : x ∈ M.C) :
    |uStar M θ x - uStar M θ₀ x| ≤ |θ - θ₀| * v₁ x := by
  have hnn : 0 ≤ |θ - θ₀| * v₁ x := mul_nonneg (abs_nonneg _) (H.hv₁_nn x hx)
  rw [← enorm_le_ofReal_iff_abs _ _ hnn, (H.identity θ hθ x hx).2]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine le_trans ?_ (H.lip_integral θ hθ x hx)
  exact lintegral_mono fun y => enorm_add_le _ _

lemma continuousAt_u (x : S) (hx : x ∈ M.C) : ContinuousAt (fun θ => uStar M θ x) θ₀ := by
  rw [Metric.continuousAt_iff]
  intro e he
  have hv : 0 < v₁ x + 1 := by linarith [H.hv₁_nn x hx]
  refine ⟨min ε (e / (v₁ x + 1)), lt_min H.hε (div_pos he hv), fun θ hθ => ?_⟩
  rw [Real.dist_eq] at hθ ⊢
  have h1 : |θ - θ₀| < ε := lt_of_lt_of_le hθ (min_le_left _ _)
  have h2 : |θ - θ₀| < e / (v₁ x + 1) := lt_of_lt_of_le hθ (min_le_right _ _)
  have hmem : θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε) := by
    rw [abs_lt] at h1; constructor <;> linarith
  calc |uStar M θ x - uStar M θ₀ x| ≤ |θ - θ₀| * v₁ x := H.lip_u θ hmem x hx
    _ ≤ |θ - θ₀| * (v₁ x + 1) := by gcongr; linarith
    _ < e / (v₁ x + 1) * (v₁ x + 1) := by gcongr
    _ = e := div_mul_cancel₀ e hv.ne'

end Hyp

end LyapDiffMC.RandomHorizon.Aux

open LyapDiffMC.RandomHorizon in
theorem solution {S : Type*} [MeasurableSpace S] (M : Setting S)
    (a b θ₀ ε : ℝ) (hθ₀ : θ₀ ∈ Set.Ioo a b) (hε : 0 < ε)
    (hεΛ : Set.Icc (θ₀ - ε) (θ₀ + ε) ⊆ Set.Ioo a b)
    (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Ioo a b, Measurable (Function.uncurry (k θ)))
    -- A1 and A3: K(θ, x, dy) = k(θ, x, y) K(θ₀, x, dy) for x ∈ C, y ∈ C and y ∈ Cᶜ
    (hA13 : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C,
      discKernel M θ x = (discKernel M θ₀ x).withDensity (fun y => ENNReal.ofReal (k θ x y)))
    (hk_nonneg : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C, ∀ᵐ y ∂(discKernel M θ₀ x), 0 ≤ k θ x y)
    -- A2 and A3: k(·, x, y) is continuously differentiable on [θ₀ - ε, θ₀ + ε]
    (hA2 : ∀ x ∈ M.C, ∀ y, ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)))
    -- A3: r̃_ε(x) < ∞
    (hA3 : ∀ x ∈ M.C, rtilde M k θ₀ ε x < ⊤)
    -- f̃(θ, x) in (3.11) is a real number
    (hf_int : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      IntegrableOn M.f M.Cᶜ (discKernel M θ x))
    (v₀ v₁ : S → ℝ) (hv₀ : Measurable v₀) (hv₁ : Measurable v₁)
    (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x) (hv₁_nn : ∀ x ∈ M.C, 0 ≤ v₁ x)
    -- (3.11)
    (h311 : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₀ y) ∂(discKernel M θ x) + ‖ftilde M θ x‖ₑ
        ≤ ENNReal.ofReal (v₀ x))
    -- (3.12)
    (h312 : ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₁ y) ∂(discKernel M θ₀ x)
        + ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₀ y) ∂(discKernel M θ₀ x)
        + rtilde M k θ₀ ε x ≤ ENNReal.ofReal (v₁ x)) :
    (∀ h : ℝ, |h| < ε → ∀ x ∈ M.C,
      ∫⁻ y, (‖(∫ z in M.C, uStar M (θ₀ + h) z ∂(discKernel M (θ₀ + h) y))
              - ∫ z in M.C, uStar M (θ₀ + h) z ∂(discKernel M θ₀ y)‖ₑ
            + ‖ftilde M (θ₀ + h) y - ftilde M θ₀ y‖ₑ) ∂(greenMeasure M θ₀ x)
        ≤ ENNReal.ofReal (|h| * v₁ x)) ∧
    ∀ x ∈ M.C, ContinuousAt (fun θ => uStar M θ x) θ₀ := by
  have H : LyapDiffMC.RandomHorizon.Aux.Hyp M a b θ₀ ε k v₀ v₁ :=
    ⟨hθ₀, hε, hεΛ, hk_meas, hA13, hk_nonneg, hA2, hA3, hf_int, hv₀, hv₁, hv₀_nn, hv₁_nn, h311,
      h312⟩
  refine ⟨fun h hh x hx => ?_, fun x hx => H.continuousAt_u x hx⟩
  have hmem : θ₀ + h ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε) := by
    rw [abs_lt] at hh; constructor <;> linarith
  have := H.lip_integral (θ₀ + h) hmem x hx
  simpa using this
