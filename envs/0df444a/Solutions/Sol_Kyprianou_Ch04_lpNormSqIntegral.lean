-- Prove2me | solution 1 for Kyprianou.Ch04.lpNormSqIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:47:30.521511+00:00
-- url     : https://prove2.me/submissions/aff04cf7-e135-495b-8e39-73c16226adff

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false
universe u

/-- The square of the L2 norm is the second moment. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : MemLp X 2 P) :
    ‖hX.toLp X‖ ^ 2 = ∫ ω, (X ω) ^ 2 ∂P := by
  rw [Lp.norm_toLp, hX.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have hnonneg : 0 ≤ ∫ ω, (X ω) ^ 2 ∂P :=
    integral_nonneg (fun ω => sq_nonneg (X ω))
  have heq : (∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂P) = ∫ ω, (X ω) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have ht : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [ht, heq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt hnonneg
