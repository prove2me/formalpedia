-- Prove2me | solution 1 for MeasureTheory.analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3e3d2aed-f6a6-5141-b421-08c168cd3f23

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable

set_option autoImplicit false

open MeasureTheory

theorem solution
    (P : ℝ → ℝ) (x₀ : ℝ) (hP : Measurable P) (hP0 : ∀ y : ℝ, 0 ≤ P y)
    (hPint : ∀ σ : ℝ, x₀ < σ → Integrable (fun y : ℝ => P y * |y| ^ (σ - 2))) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) {s : ℂ | x₀ < s.re} ∧
    (∀ σ : ℝ, x₀ < σ →
      (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).im = 0 ∧
      0 ≤ (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).re) ∧
    ((¬ ∀ᵐ y : ℝ, P y = 0) → ∀ σ : ℝ, x₀ < σ →
      0 < (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).re) := by

  set F : ℂ → ℝ → ℂ := fun s y => ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2) with hF
  have ae_ne0 : ∀ᵐ y : ℝ ∂volume, y ≠ (0 : ℝ) := by
    have hc : ({0} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.mpr Real.volume_singleton
    filter_upwards [hc] with x hx
    simpa using hx
  have rpow_le_add : ∀ t : ℝ, 0 < t → ∀ a b σ : ℝ, a ≤ σ → σ ≤ b → t ^ σ ≤ t ^ a + t ^ b := by
    intro t ht a b σ h1 h2
    rcases le_or_gt 1 t with h | h
    · exact le_add_of_nonneg_of_le (Real.rpow_nonneg ht.le _) (Real.rpow_le_rpow_of_exponent_le h h2)
    · exact le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_ge ht h.le h1) (Real.rpow_nonneg ht.le _)
  have abs_log_le : ∀ t : ℝ, 0 < t → ∀ δ : ℝ, 0 < δ → |Real.log t| ≤ (t ^ δ + t ^ (-δ)) / δ := by
    intro t ht δ hδ
    have h1 : Real.log t ≤ t ^ δ / δ := Real.log_le_rpow_div ht.le hδ
    have h2 : -Real.log t ≤ t ^ (-δ) / δ := by
      have := Real.log_le_rpow_div (inv_nonneg.mpr ht.le) hδ
      rw [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this
      exact this
    have h3 : 0 ≤ t ^ δ / δ := div_nonneg (Real.rpow_nonneg ht.le _) hδ.le
    have h4 : 0 ≤ t ^ (-δ) / δ := div_nonneg (Real.rpow_nonneg ht.le _) hδ.le
    rw [abs_le, add_div]
    constructor <;> linarith
  have normF : ∀ (s : ℂ) (y : ℝ), y ≠ 0 → ‖F s y‖ = P y * |y| ^ (s.re - 2) := by
    intro s y hy
    simp only [hF]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP0 y),
      Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hy)]
    simp
  have meas_cpow : ∀ s : ℂ, Measurable fun y : ℝ => ((|y| : ℝ) : ℂ) ^ (s - 2) := fun s =>
    (Complex.measurable_ofReal.comp continuous_abs.measurable).pow_const _
  have measF : ∀ s : ℂ, AEStronglyMeasurable (F s) volume := by
    intro s
    simp only [hF]
    exact ((Complex.measurable_ofReal.comp hP).mul (meas_cpow s)).aestronglyMeasurable
  have intF : ∀ s : ℂ, x₀ < s.re → Integrable (F s) := by
    intro s hs
    refine (hPint s.re hs).mono' (measF s) ?_
    filter_upwards [ae_ne0] with y hy
    rw [normF s y hy]

  have hderiv : ∀ s₀ : ℂ, x₀ < s₀.re → DifferentiableAt ℂ (fun s => ∫ y : ℝ, F s y) s₀ := by
    intro s₀ hs₀
    obtain ⟨δ, hδ, hδ'⟩ : ∃ δ : ℝ, 0 < δ ∧ x₀ < s₀.re - 2 * δ :=
      ⟨(s₀.re - x₀) / 4, by linarith, by linarith⟩
    set a : ℝ := s₀.re - 2 * δ with ha
    set b : ℝ := s₀.re + 2 * δ with hb
    have hxa : x₀ < a := hδ'
    have hxb : x₀ < b := by rw [hb]; linarith
    set F' : ℂ → ℝ → ℂ := fun s y =>
      ((P y : ℝ) : ℂ) * (((|y| : ℝ) : ℂ) ^ (s - 2) * Complex.log ((|y| : ℝ) : ℂ)) with hF'
    set bound : ℝ → ℝ := fun y => P y * |y| ^ (a - 2) * (2 / δ) + P y * |y| ^ (b - 2) * (2 / δ) with hbound
    have measF' : AEStronglyMeasurable (F' s₀) volume := by
      simp only [hF']
      exact ((Complex.measurable_ofReal.comp hP).mul ((meas_cpow s₀).mul
        (Complex.measurable_log.comp (Complex.measurable_ofReal.comp continuous_abs.measurable)))).aestronglyMeasurable
    have hbound_int : Integrable bound := by
      simp only [hbound]
      exact ((hPint a hxa).mul_const _).add ((hPint b hxb).mul_const _)
    have h_bound : ∀ᵐ y : ℝ ∂volume, ∀ s ∈ Metric.ball s₀ δ, ‖F' s y‖ ≤ bound y := by
      filter_upwards [ae_ne0] with y hy
      intro s hs
      have hy' : 0 < |y| := abs_pos.mpr hy
      have hre : |s.re - s₀.re| < δ := by
        have := Metric.mem_ball.mp hs
        rw [Complex.dist_eq] at this
        exact lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀)) this
      simp only [hF', hbound]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP0 y),
        Complex.norm_cpow_eq_rpow_re_of_pos hy', ← Complex.ofReal_log hy'.le, Complex.norm_real,
        Real.norm_eq_abs]
      have hlog := abs_log_le |y| hy' δ hδ
      have hσ1 : |y| ^ ((s - 2).re + δ) ≤ |y| ^ (a - 2) + |y| ^ (b - 2) := by
        apply rpow_le_add |y| hy'
        · simp; rw [abs_lt] at hre; linarith
        · simp; rw [abs_lt] at hre; linarith
      have hσ2 : |y| ^ ((s - 2).re - δ) ≤ |y| ^ (a - 2) + |y| ^ (b - 2) := by
        apply rpow_le_add |y| hy'
        · simp; rw [abs_lt] at hre; linarith
        · simp; rw [abs_lt] at hre; linarith
      have hP0y := hP0 y
      have key : |y| ^ (s - 2).re * abs (Real.log |y|) ≤ (|y| ^ (a - 2) + |y| ^ (b - 2)) * (2 / δ) := by
        calc |y| ^ (s - 2).re * abs (Real.log |y|) ≤ |y| ^ (s - 2).re * ((|y| ^ δ + |y| ^ (-δ)) / δ) :=
              mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hy'.le _)
          _ = (|y| ^ ((s - 2).re + δ) + |y| ^ ((s - 2).re - δ)) / δ := by
              rw [Real.rpow_add hy', Real.rpow_sub hy', Real.rpow_neg hy'.le]; ring
          _ ≤ ((|y| ^ (a - 2) + |y| ^ (b - 2)) + (|y| ^ (a - 2) + |y| ^ (b - 2))) / δ := by
              gcongr
          _ = (|y| ^ (a - 2) + |y| ^ (b - 2)) * (2 / δ) := by ring
      calc P y * (|y| ^ (s - 2).re * abs (Real.log |y|)) ≤ P y * ((|y| ^ (a - 2) + |y| ^ (b - 2)) * (2 / δ)) :=
            mul_le_mul_of_nonneg_left key hP0y
        _ = P y * |y| ^ (a - 2) * (2 / δ) + P y * |y| ^ (b - 2) * (2 / δ) := by ring
    have h_diff : ∀ᵐ y : ℝ ∂volume, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (fun s => F s y) (F' s y) s := by
      filter_upwards [ae_ne0] with y hy
      intro s _
      have hyC : ((|y| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hy)
      simp only [hF, hF']
      have h1 : HasDerivAt (fun s : ℂ => ((|y| : ℝ) : ℂ) ^ (s - 2))
          (((|y| : ℝ) : ℂ) ^ (s - 2) * Complex.log ((|y| : ℝ) : ℂ) * 1) s :=
        (Complex.hasStrictDerivAt_const_cpow (Or.inl hyC)).hasDerivAt.comp s ((hasDerivAt_id s).sub_const 2)
      rw [mul_one] at h1
      exact h1.const_mul _
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s₀ hδ)
      (Filter.Eventually.of_forall measF) (intF s₀ hs₀) measF' h_bound hbound_int h_diff).2.differentiableAt
  have hopen : IsOpen {s : ℂ | x₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re

  have hrealint : ∀ σ : ℝ, (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)) =
      ((∫ y : ℝ, P y * |y| ^ (σ - 2) : ℝ) : ℂ) := by
    intro σ
    rw [← integral_complex_ofReal]
    congr 1
    funext y
    rw [show ((σ : ℂ) - 2) = ((σ - 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (abs_nonneg y)]
    push_cast
    ring
  have hA : AnalyticOnNhd ℂ (fun s => ∫ y : ℝ, F s y) {s : ℂ | x₀ < s.re} :=
    DifferentiableOn.analyticOnNhd (fun s hs => (hderiv s hs).differentiableWithinAt) hopen
  refine ⟨hA, ?_, ?_⟩
  · intro σ hσ
    rw [hrealint σ]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    exact integral_nonneg fun y => mul_nonneg (hP0 y) (Real.rpow_nonneg (abs_nonneg y) _)
  · intro hPne σ hσ
    rw [hrealint σ, Complex.ofReal_re]
    refine (integral_pos_iff_support_of_nonneg (fun y => mul_nonneg (hP0 y) (Real.rpow_nonneg (abs_nonneg y) _))
      (hPint σ hσ)).mpr ?_

    have hsupp : Function.support P \ {0} ⊆ Function.support (fun y : ℝ => P y * |y| ^ (σ - 2)) := by
      intro y hy
      rcases hy with ⟨h1, h2⟩
      have h2' : y ≠ 0 := h2
      exact mul_ne_zero h1 (Real.rpow_pos_of_pos (abs_pos.mpr h2') _).ne'
    have hpos : 0 < (volume : Measure ℝ) (Function.support P) := by
      rw [pos_iff_ne_zero]
      intro h0
      apply hPne
      have : ∀ᵐ y : ℝ ∂volume, y ∉ Function.support P := compl_mem_ae_iff.mpr h0 |> fun h => by
        filter_upwards [h] with y hy; exact hy
      filter_upwards [this] with y hy
      simpa [Function.mem_support] using hy
    calc (0 : ENNReal) < volume (Function.support P) := hpos
      _ = volume (Function.support P \ {0}) := (measure_diff_null Real.volume_singleton).symm
      _ ≤ volume (Function.support (fun y : ℝ => P y * |y| ^ (σ - 2))) := measure_mono hsupp

end S_MeasureTheory_analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable
end P2MW
export P2MW.S_MeasureTheory_analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable (solution)
