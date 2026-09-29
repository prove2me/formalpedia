-- Prove2me | solution 1 for MeasureTheory.exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7307b294-a1cb-5b0c-be77-3f24a73e7159

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate ContDiff

namespace BK9

open scoped FourierTransform RealInnerProductSpace

noncomputable def g₀ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

noncomputable def g (x : ℝ) : ℂ := ((g₀ : ℝ → ℝ) x : ℂ)

lemma g_contDiff : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp g₀.contDiff

lemma g_continuous : Continuous g := g_contDiff.continuous

lemma g_hasCompactSupport : HasCompactSupport g :=
  g₀.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero

lemma g_zero : g 0 = 1 := by
  unfold g
  rw [g₀.one_of_mem_closedBall (Metric.mem_closedBall_self g₀.rIn_pos.le)]
  simp

lemma g_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : g x = 0 := by
  unfold g
  have : (g₀ : ℝ → ℝ) x = 0 := by
    rw [← Function.notMem_support, g₀.support_eq]
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact hx
  rw [this]; simp

lemma conj_g (x : ℝ) : conj (g x) = g x := by unfold g; exact Complex.conj_ofReal _

lemma g_integrable : Integrable g := g_continuous.integrable_of_hasCompactSupport g_hasCompactSupport

lemma iteratedDeriv_g_hasCompactSupport (n : ℕ) : HasCompactSupport (iteratedDeriv n g) := by
  have h := (g_hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) n).comp_left
    (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ => L fun _ => 1) (by simp)
  have : iteratedDeriv n g = (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ => L fun _ => 1) ∘
      iteratedFDeriv ℝ n g := by
    funext x; rw [iteratedDeriv_eq_iteratedFDeriv]; rfl
  rw [this]; exact h

lemma iteratedDeriv_g_integrable (n : ℕ) : Integrable (iteratedDeriv n g) :=
  (g_contDiff.continuous_iteratedDeriv n (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    (iteratedDeriv_g_hasCompactSupport n)

noncomputable def Φ : ℝ → ℂ := 𝓕 g

noncomputable def ρ (t : ℝ) : ℝ := (Φ t).re

lemma Φ_continuous : Continuous Φ :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ g_integrable

lemma ρ_continuous : Continuous ρ := Complex.continuous_re.comp Φ_continuous

lemma Φ_decay (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, |w| ^ n * ‖Φ w‖ ≤ C := by
  have key := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (n := n) g_contDiff
    (fun k _ => iteratedDeriv_g_integrable k) le_top
  set L : ℝ := ∫ v : ℝ, ‖iteratedDeriv n g v‖ with hL
  refine ⟨L / (2 * Real.pi) ^ n, by positivity, fun w => ?_⟩
  have h1 : ‖𝓕 (iteratedDeriv n g) w‖ ≤ L :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [key] at h1
  simp only [norm_smul, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h1
  rw [le_div_iff₀ (by positivity)]
  calc |w| ^ n * ‖Φ w‖ * (2 * Real.pi) ^ n = (2 * Real.pi * |w|) ^ n * ‖𝓕 g w‖ := by rw [Φ]; ring
    _ ≤ L := h1

lemma Φ_decay₂ (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, |w| ^ n * ‖Φ w‖ ≤ C * (1 + w ^ 2)⁻¹ := by
  obtain ⟨C₀, hC₀, h₀⟩ := Φ_decay n
  obtain ⟨C₂, hC₂, h₂⟩ := Φ_decay (n + 2)
  refine ⟨C₀ + C₂, by positivity, fun w => ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have := h₂ w
  have e : |w| ^ (n + 2) = |w| ^ n * w ^ 2 := by rw [pow_add, sq_abs]
  rw [e] at this
  nlinarith [h₀ w, norm_nonneg (Φ w), pow_nonneg (abs_nonneg w) n]

lemma integrable_pow_mul_norm_Φ (n : ℕ) : Integrable (fun t : ℝ => |t| ^ n * ‖Φ t‖) := by
  obtain ⟨C, hC, h⟩ := Φ_decay₂ n
  refine ((integrable_inv_one_add_sq).const_mul C).mono' ?_ (ae_of_all _ fun t => ?_)
  · exact ((continuous_abs.pow n).mul Φ_continuous.norm).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]; exact h t

lemma Φ_integrable : Integrable Φ := by
  refine (integrable_pow_mul_norm_Φ 0).mono' Φ_continuous.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  simp

lemma ρ_moment (n : ℕ) : Integrable (fun t : ℝ => |t| ^ n * ρ t) := by
  refine (integrable_pow_mul_norm_Φ n).mono' ((continuous_abs.pow n).mul ρ_continuous).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)

lemma integral_ρ : ∫ t : ℝ, ρ t = 1 := by
  have h1 : ∫ t : ℝ, ρ t = (∫ t : ℝ, Φ t).re := by
    unfold ρ
    exact integral_re Φ_integrable
  have h2 : ∫ t : ℝ, Φ t = 𝓕⁻ Φ 0 := by
    rw [Real.fourierInv_eq]
    simp
  have h3 : 𝓕⁻ Φ 0 = g 0 := by
    unfold Φ
    rw [g_continuous.fourierInv_fourier_eq g_integrable Φ_integrable]
  rw [h1, h2, h3, g_zero, Complex.one_re]

noncomputable def Gs (δ : ℝ) (z : ℝ) : ℂ :=
  (g ((δ / (2 * Real.pi)) * z) + g ((-(δ / (2 * Real.pi))) * z)) / 2

lemma hasCompactSupport_g_comp (c : ℝ) (hc : c ≠ 0) : HasCompactSupport (fun z : ℝ => g (c * z)) :=
  g_hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft₀ c hc)

lemma continuous_g_comp (c : ℝ) : Continuous (fun z : ℝ => g (c * z)) :=
  g_continuous.comp (continuous_const.mul continuous_id)

lemma contDiff_g_comp (c : ℝ) : ContDiff ℝ ∞ (fun z : ℝ => g (c * z)) :=
  g_contDiff.comp (contDiff_const.mul contDiff_id)

lemma Gs_contDiff (δ : ℝ) : ContDiff ℝ ∞ (Gs δ) :=
  ((contDiff_g_comp _).add (contDiff_g_comp _)).div_const _

lemma Gs_continuous (δ : ℝ) : Continuous (Gs δ) := (Gs_contDiff δ).continuous

lemma Gs_hasCompactSupport (δ : ℝ) (hδ : 0 < δ) : HasCompactSupport (Gs δ) := by
  have h1 := hasCompactSupport_g_comp (δ / (2 * Real.pi)) (by positivity)
  have h2 := hasCompactSupport_g_comp (-(δ / (2 * Real.pi))) (by
    have : 0 < δ / (2 * Real.pi) := by positivity
    linarith)
  exact ((h1.add h2).mul_left (f := fun _ => (1 / 2 : ℂ))).mono (by
    intro z hz
    simp only [Function.mem_support, Gs] at hz ⊢
    intro h; apply hz; rw [show (g (δ / (2 * Real.pi) * z) + g (-(δ / (2 * Real.pi)) * z)) = 0 by
      simpa using h]; simp)

lemma Gs_integrable (δ : ℝ) (hδ : 0 < δ) : Integrable (Gs δ) :=
  (Gs_continuous δ).integrable_of_hasCompactSupport (Gs_hasCompactSupport δ hδ)

lemma Φ_eq (w : ℝ) : Φ w = ∫ v : ℝ, Complex.exp (((-2 * Real.pi * v * w : ℝ) : ℂ) * Complex.I) * g v := by
  unfold Φ
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]

lemma conj_Φ_eq (w : ℝ) : conj (Φ w) = ∫ v : ℝ, Complex.exp (((2 * Real.pi * v * w : ℝ) : ℂ) * Complex.I) * g v := by
  rw [Φ_eq, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [map_mul, conj_g]
  rw [← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

lemma integral_subst (c : ℝ) (hc : c ≠ 0) (F : ℝ → ℂ) :
    ∫ v : ℝ, F v = |c| * ∫ z : ℝ, F (c * z) := by
  have := Measure.integral_comp_mul_left F c
  rw [this, abs_inv, Complex.real_smul, ← mul_assoc]
  rw [show ((|c| : ℝ) : ℂ) * ((|c|⁻¹ : ℝ) : ℂ) = 1 by
    push_cast; field_simp [abs_ne_zero.mpr hc]]
  rw [one_mul]

lemma kernel_identity (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    ((δ⁻¹ * ρ (s / δ) : ℝ) : ℂ) =
      ((2 * Real.pi)⁻¹ : ℝ) * ∫ z : ℝ, Gs δ z * Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  set c : ℝ := δ / (2 * Real.pi) with hcdef
  have hc : 0 < c := by positivity

  have hρ : ((ρ (s / δ) : ℝ) : ℂ) = (Φ (s / δ) + conj (Φ (s / δ))) / 2 := by
    unfold ρ; rw [Complex.re_eq_add_conj]

  have hδC : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have e1 : Φ (s / δ) = ((c : ℝ) : ℂ) * ∫ z : ℝ, Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g ((-c) * z) := by
    rw [Φ_eq, integral_subst (-c) (by linarith) _, abs_neg, abs_of_pos hc]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show Complex.exp (((-2 * Real.pi * ((-c) * z) * (s / δ) : ℝ) : ℂ) * Complex.I) * g ((-c) * z) =
      Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g ((-c) * z)
    have hX : ((-2 * Real.pi * ((-c) * z) * (s / δ) : ℝ) : ℂ) * Complex.I = (s : ℂ) * Complex.I * (z : ℂ) := by
      rw [hcdef]; push_cast; field_simp
    rw [hX]
  have e2 : conj (Φ (s / δ)) = ((c : ℝ) : ℂ) * ∫ z : ℝ, Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g (c * z) := by
    rw [conj_Φ_eq, integral_subst c hc.ne' _, abs_of_pos hc]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show Complex.exp (((2 * Real.pi * (c * z) * (s / δ) : ℝ) : ℂ) * Complex.I) * g (c * z) =
      Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g (c * z)
    have hX : ((2 * Real.pi * (c * z) * (s / δ) : ℝ) : ℂ) * Complex.I = (s : ℂ) * Complex.I * (z : ℂ) := by
      rw [hcdef]; push_cast; field_simp
    rw [hX]
  have hi1 : Integrable (fun z : ℝ => Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g ((-c) * z)) :=
    ((Complex.continuous_exp.comp ((continuous_const).mul Complex.continuous_ofReal)).mul
      (continuous_g_comp _)).integrable_of_hasCompactSupport
      ((hasCompactSupport_g_comp (-c) (by linarith)).mul_left)
  have hi2 : Integrable (fun z : ℝ => Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g (c * z)) :=
    ((Complex.continuous_exp.comp ((continuous_const).mul Complex.continuous_ofReal)).mul
      (continuous_g_comp _)).integrable_of_hasCompactSupport
      ((hasCompactSupport_g_comp c hc.ne').mul_left)
  rw [Complex.ofReal_mul, hρ, e2, e1, ← mul_add, ← integral_add hi1 hi2]
  have e3 : ∫ z : ℝ, Gs δ z * Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) =
      (1 / 2 : ℂ) * ∫ z : ℝ, (Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g ((-c) * z) +
        Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g (c * z)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [Gs, hcdef]
    ring
  rw [e3, hcdef]
  push_cast
  field_simp

lemma norm_cexp_mul_I_mul (a z : ℝ) : ‖Complex.exp ((a : ℂ) * Complex.I * (z : ℂ))‖ = 1 := by
  rw [show (a : ℂ) * Complex.I * (z : ℂ) = ((a * z : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

lemma integrable_pow_mul_norm_of_bdd {u : ℝ → ℂ} (hu : Measurable u) {R B : ℝ}
    (hR : ∀ x, R < |x| → u x = 0) (hB : ∀ x, ‖u x‖ ≤ B) (n : ℕ) :
    Integrable (fun x : ℝ => ‖x‖ ^ n * ‖u x‖) := by
  have hB0 : ∀ x, 0 ≤ B := fun x => (norm_nonneg _).trans (hB x)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ‖x‖ ^ n * ‖u x‖) volume :=
    ((continuous_norm.pow n).measurable.mul hu.norm).aestronglyMeasurable
  refine (((integrableOn_const (measure_Icc_lt_top (a := -R) (b := R)).ne).integrable_indicator
    measurableSet_Icc : Integrable ((Set.Icc (-R) R).indicator fun _ => |R| ^ n * B))).mono'
    hmeas (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) n) (norm_nonneg _))]
  by_cases hx : x ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hx]
    have : ‖x‖ ≤ |R| := by rw [Real.norm_eq_abs]; exact (abs_le.mpr hx).trans (le_abs_self R)
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) this n) (hB x) (norm_nonneg _) (by positivity)
  · rw [Set.indicator_of_notMem hx]
    have : R < |x| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
      · exact lt_of_lt_of_le h (le_abs_self x)
    rw [hR x this, norm_zero, mul_zero]

end BK9

theorem solution :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ n : ℕ, Integrable (fun t : ℝ => |t| ^ n * ρ t)) ∧ (∫ t : ℝ, ρ t = 1) ∧
      ∀ (u : ℝ → ℂ), Measurable u → (∃ R : ℝ, ∀ x, R < |x| → u x = 0) → (∃ B : ℝ, ∀ x, ‖u x‖ ≤ B) →
      ∀ δ : ℝ, 0 < δ →
      ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
        ∀ t : ℝ, (∫ x : ℝ, u x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) =
          ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) := by
  open scoped FourierTransform in
  refine ⟨BK9.ρ, BK9.ρ_continuous.measurable, BK9.ρ_moment, BK9.integral_ρ, ?_⟩
  intro u hu hR hB δ hδ
  obtain ⟨R, hR⟩ := hR
  obtain ⟨B, hB⟩ := hB
  have hmom : ∀ n : ℕ, Integrable (fun x : ℝ => ‖x‖ ^ n * ‖u x‖) :=
    fun n => BK9.integrable_pow_mul_norm_of_bdd hu hR hB n
  have hu_int : Integrable u := (hmom 0).mono' hu.aestronglyMeasurable (ae_of_all _ fun x => by simp)
  have hFu : ContDiff ℝ ∞ (𝓕 u) := Real.contDiff_fourier (N := (⊤ : ℕ∞)) (fun n _ => hmom n)
  set h : ℝ → ℂ := fun z => (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (BK9.Gs δ z * 𝓕 u (z / (2 * Real.pi))) with hh
  refine ⟨h, ?_, ?_, ?_⟩
  · exact contDiff_const.mul ((BK9.Gs_contDiff δ).mul (hFu.comp (contDiff_id.div_const _)))
  · have : HasCompactSupport (fun z : ℝ => BK9.Gs δ z * 𝓕 u (z / (2 * Real.pi))) :=
      (BK9.Gs_hasCompactSupport δ hδ).mul_right
    exact this.mul_left
  · intro t

    set F : ℝ → ℝ → ℂ := fun x z => (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      (u x * (BK9.Gs δ z * Complex.exp (((t - x : ℝ) : ℂ) * Complex.I * (z : ℂ)))) with hF
    have step1 : (∫ x : ℝ, u x * ((δ⁻¹ * BK9.ρ ((t - x) / δ) : ℝ) : ℂ)) = ∫ x : ℝ, ∫ z : ℝ, F x z := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hF]
      rw [BK9.kernel_identity δ hδ (t - x), ← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only
      ring
    have hFint : Integrable (Function.uncurry F) ((volume : Measure ℝ).prod volume) := by
      have hg : Integrable (fun p : ℝ × ℝ => (2 * Real.pi)⁻¹ * (‖u p.1‖ * ‖BK9.Gs δ p.2‖)) ((volume : Measure ℝ).prod volume) :=
        (hu_int.norm.mul_prod (BK9.Gs_integrable δ hδ).norm).const_mul _
      refine hg.mono' ?_ (ae_of_all _ fun p => ?_)
      · have m1 : AEStronglyMeasurable (fun p : ℝ × ℝ => u p.1) ((volume : Measure ℝ).prod volume) :=
          (hu.comp measurable_fst).aestronglyMeasurable
        have m2 : Continuous (fun p : ℝ × ℝ => BK9.Gs δ p.2 *
            Complex.exp (((t - p.1 : ℝ) : ℂ) * Complex.I * (p.2 : ℂ))) := by
          refine ((BK9.Gs_continuous δ).comp continuous_snd).mul (Complex.continuous_exp.comp ?_)
          exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).mul continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_snd)
        exact (m1.mul m2.aestronglyMeasurable).const_mul _
      · rcases p with ⟨x, z⟩
        simp only [Function.uncurry_apply_pair, hF, norm_mul, BK9.norm_cexp_mul_I_mul, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        exact le_rfl
    rw [step1, integral_integral_swap hFint]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)

    have hpt : ∀ x : ℝ, F x z = ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * BK9.Gs δ z * Complex.exp ((t : ℂ) * Complex.I * (z : ℂ))) *
        (Complex.exp (((-2 * Real.pi * x * (z / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) • u x) := by
      intro x
      simp only [hF, smul_eq_mul]
      have : Complex.exp (((t - x : ℝ) : ℂ) * Complex.I * (z : ℂ)) =
          Complex.exp ((t : ℂ) * Complex.I * (z : ℂ)) * Complex.exp (((-2 * Real.pi * x * (z / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
        push_cast
        field_simp
        ring
      rw [this]
      ring
    simp_rw [hpt]
    rw [integral_const_mul, ← Real.fourier_real_eq_integral_exp_smul]
    simp only [hh]
    ring

end S_MeasureTheory_exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp
end P2MW
export P2MW.S_MeasureTheory_exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp (solution)
