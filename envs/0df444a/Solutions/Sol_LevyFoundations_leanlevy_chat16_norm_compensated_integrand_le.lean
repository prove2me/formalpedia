-- Prove2me | solution 1 for LevyFoundations.leanlevy_chat16_norm_compensated_integrand_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:56:15.678878+00:00
-- url     : https://prove2.me/submissions/ba092740-7faf-47ea-8902-96f7a9ab7050

import Mathlib
import Definitions.Def_levy_foundations_compensatedIntegrand

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex

theorem solution (ξ x : ℝ) :
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
