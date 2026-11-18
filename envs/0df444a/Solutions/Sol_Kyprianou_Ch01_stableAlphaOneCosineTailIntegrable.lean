-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineTailIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:34:35.20255+00:00
-- url     : https://prove2.me/submissions/18ef46bb-fa30-4821-a979-59b86c70e1db

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! The stable-alpha-one cosine integrand has an integrable tail. -/
theorem solution :
    IntegrableOn (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
    (Set.Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by norm_num)
  have htwo : IntegrableOn (fun r : ℝ => 2 * r ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
    hpow.const_mul 2
  apply htwo.mono'
  · have hm : Measurable (fun r : ℝ => (1 - Real.cos r) / r ^ 2) := by
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrpos : 0 < r := (by norm_num : (0 : ℝ) < 1).trans hr
    have hbound : 0 ≤ 1 - Real.cos r ∧ 1 - Real.cos r ≤ 2 := by
      constructor
      · linarith [Real.cos_le_one r]
      · linarith [Real.neg_one_le_cos r]
    have hrpow : r ^ (-2 : ℝ) = (r ^ 2)⁻¹ := by
      rw [Real.rpow_neg hrpos.le]
      exact congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast r 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hbound.1 (sq_nonneg r)),
      hrpow]
    apply div_le_iff₀ (pow_pos hrpos _)|>.mpr
    field_simp
    linarith [hbound.2]
