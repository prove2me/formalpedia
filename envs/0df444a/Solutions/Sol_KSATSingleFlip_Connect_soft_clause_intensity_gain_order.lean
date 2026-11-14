-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_clause_intensity_gain_order
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:51:28.475197+00:00
-- url     : https://prove2.me/submissions/2ba23f6e-75e6-40b9-ac40-4cb0ea799fbd

import Theorems.Thm_KSATSingleFlip_Connect_soft_clause_intensity_integral
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_order_clause_gain
import Theorems.Thm_KSATSingleFlip_Connect_soft_clause_gain_continuous
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect Set

theorem solution (ν' ν : Measure ℝ) (hord : softFieldLE ν' ν)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc 0 1)) (hψ : ConcaveOn ℝ (Icc 0 1) ψ)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (v0 v1 : ℝ) (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) :
    (∫ s, (Icc 0 1).indicator (softClauseGain ψ v0 v1) s ∂(softClauseIntensity ν')) ≤
      ∫ s, (Icc 0 1).indicator (softClauseGain ψ v0 v1) s ∂(softClauseIntensity ν) := by
  have hc' := soft_clause_gain_continuous ψ hc hψ0 hψ1 v0 v1 hv0 hv1
  rw [soft_clause_intensity_integral ν' _ hc', soft_clause_intensity_integral ν _ hc']
  exact mul_le_mul_of_nonneg_left (soft_field_order_clause_gain ν' ν hord ψ hc hψ hψ0 hψ1 v0 v1 hv0 hv1) (by norm_num)
