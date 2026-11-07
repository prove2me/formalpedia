-- Prove2me | solution 1 for LevyFoundations.leanlevy_chat16_compensated_integral_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:12:13.392575+00:00
-- url     : https://prove2.me/submissions/6d886585-5393-471f-afca-1db73053b5cf

import Mathlib
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_compensatedIntegrand

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter
open scoped Topology

private theorem chat16_integrand_norm_bound (ξ x : ℝ) :
    ‖LevyFoundations.compensatedIntegrand ξ x‖ ≤
      (2 + 3 * ξ ^ 2) * min 1 (x ^ 2) := by
  by_cases hx : |x| < 1
  · have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
    have hmin : min (1 : ℝ) (x ^ 2) = x ^ 2 := min_eq_right (le_of_lt hx2)
    rw [hmin]
    simp only [LevyFoundations.compensatedIntegrand, hx, ite_true, mul_one]
    set z : ℂ := ↑x * ↑ξ * I with hz_def
    have hz_eq : z = ↑(x * ξ) * I := by push_cast; ring
    have hz_norm : ‖z‖ = |x * ξ| := by
      rw [hz_eq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]
    by_cases hxξ : |x * ξ| ≤ 1
    · have hle : ‖z‖ ≤ 1 := by rw [hz_norm]; exact hxξ
      have htaylor : ‖exp z - 1 - z‖ ≤ ‖z‖ ^ 2 :=
        norm_exp_sub_one_sub_id_le hle
      calc
        ‖exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := htaylor
        _ = (x * ξ) ^ 2 := by rw [hz_norm, sq_abs]
        _ = x ^ 2 * ξ ^ 2 := by ring
        _ ≤ (2 + 3 * ξ ^ 2) * x ^ 2 := by
          nlinarith [sq_nonneg ξ, sq_nonneg x]
    · push Not at hxξ
      have hexp : ‖exp z‖ = 1 := by
        rw [hz_eq]
        exact norm_exp_ofReal_mul_I _
      have htri : ‖exp z - 1 - z‖ ≤ 2 + |x * ξ| := by
        calc
          ‖exp z - 1 - z‖ = ‖(exp z - 1) - z‖ := by ring_nf
          _ ≤ ‖exp z - 1‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ (‖exp z‖ + ‖(1 : ℂ)‖) + ‖z‖ := by
            gcongr
            exact norm_sub_le _ _
          _ = 2 + |x * ξ| := by
            rw [hexp, norm_one, hz_norm]
            ring
      have h3 : 2 + |x * ξ| ≤ 3 * (x * ξ) ^ 2 := by
        nlinarith [sq_abs (x * ξ)]
      calc
        ‖exp z - 1 - z‖ ≤ 2 + |x * ξ| := htri
        _ ≤ 3 * (x * ξ) ^ 2 := h3
        _ = 3 * ξ ^ 2 * x ^ 2 := by ring
        _ ≤ (2 + 3 * ξ ^ 2) * x ^ 2 := by nlinarith [sq_nonneg x]
  · push Not at hx
    have hmin : min (1 : ℝ) (x ^ 2) = 1 :=
      min_eq_left ((one_le_sq_iff_one_le_abs x).mpr hx)
    rw [hmin]
    have htwo : ‖LevyFoundations.compensatedIntegrand ξ x‖ ≤ 2 := by
      simp only [LevyFoundations.compensatedIntegrand,
        not_lt.mpr hx, if_false, mul_zero, sub_zero]
      calc
        ‖exp (↑x * ↑ξ * I) - 1‖
            ≤ ‖exp (↑x * ↑ξ * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by
          rw [show (↑x : ℂ) * ↑ξ * I = ↑(x * ξ) * I from by
            push_cast; ring, norm_exp_ofReal_mul_I, norm_one]
        _ = 2 := by ring
    calc
      ‖LevyFoundations.compensatedIntegrand ξ x‖ ≤ 2 := htwo
      _ ≤ (2 + 3 * ξ ^ 2) * 1 := by nlinarith [sq_nonneg ξ]

theorem solution {ν : Measure ℝ} (hν : LevyFoundations.isLevyMeasure ν) :
    Continuous (fun ξ : ℝ =>
      ∫ x, LevyFoundations.compensatedIntegrand ξ x ∂ν) := by
  have hmeas (ξ : ℝ) :
      Measurable (LevyFoundations.compensatedIntegrand ξ) := by
    unfold LevyFoundations.compensatedIntegrand
    apply Measurable.sub
    · apply Measurable.sub
      · exact (((Complex.measurable_ofReal).mul measurable_const).mul
          measurable_const).cexp
      · exact measurable_const
    · apply Measurable.mul
      · exact (Complex.measurable_ofReal.mul measurable_const).mul measurable_const
      · exact measurable_const.ite
          (isOpen_Iio.preimage continuous_abs |>.measurableSet) measurable_const
  have henv : Integrable (fun x : ℝ => min 1 (x ^ 2)) ν := by
    refine ⟨(continuous_const.min (continuous_pow 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have henorm : ∀ x : ℝ, ‖min 1 (x ^ 2)‖ₑ =
        ENNReal.ofReal (min 1 (x ^ 2)) := fun x =>
      Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg x))
    simp_rw [henorm]
    exact hν.2
  have hpoint (x : ℝ) :
      Continuous (fun ξ : ℝ => LevyFoundations.compensatedIntegrand ξ x) := by
    unfold LevyFoundations.compensatedIntegrand
    by_cases hx : |x| < 1
    · simp only [if_pos hx, mul_one]
      fun_prop
    · simp only [if_neg hx, mul_zero, sub_zero]
      fun_prop
  rw [continuous_iff_continuousAt]
  intro ξ₀
  refine continuousAt_of_dominated
    (bound := fun x => (2 + 3 * (|ξ₀| + 1) ^ 2) * min 1 (x ^ 2))
    (Eventually.of_forall fun ξ => (hmeas ξ).aestronglyMeasurable)
    ?_ (henv.const_mul _)
    (Eventually.of_forall fun x => (hpoint x).continuousAt)
  have hev : ∀ᶠ ξ in 𝓝 ξ₀, |ξ| < |ξ₀| + 1 :=
    continuous_abs.continuousAt.eventually_lt continuousAt_const (by linarith)
  filter_upwards [hev] with ξ hξ
  filter_upwards with x
  have hξ2 : ξ ^ 2 ≤ (|ξ₀| + 1) ^ 2 := by
    nlinarith [sq_abs ξ, hξ.le, abs_nonneg ξ, abs_nonneg ξ₀]
  have hmin : (0 : ℝ) ≤ min 1 (x ^ 2) :=
    le_min zero_le_one (sq_nonneg x)
  calc
    ‖LevyFoundations.compensatedIntegrand ξ x‖
        ≤ (2 + 3 * ξ ^ 2) * min 1 (x ^ 2) :=
      chat16_integrand_norm_bound ξ x
    _ ≤ (2 + 3 * (|ξ₀| + 1) ^ 2) * min 1 (x ^ 2) := by
      nlinarith [hξ2, hmin]
