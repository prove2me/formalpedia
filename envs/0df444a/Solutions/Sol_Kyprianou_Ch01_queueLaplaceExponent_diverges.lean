-- Prove2me | solution 1 for Kyprianou.Ch01.queueLaplaceExponent_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:04:50.545388+00:00
-- url     : https://prove2.me/submissions/d90406ec-7a3e-4f10-a447-8978cee6041f

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The expectation of a discounted nonnegative claim loss is at most one. -/
private theorem queueExpIntegralLeOne
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (theta : ℝ) (htheta : 0 ≤ theta) :
    (∫ x, (1 - Real.exp (-theta * x)) ∂F) ≤ 1 := by
  have hpos : ∀ᵐ x ∂F, 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hpositive] with x hx
    exact lt_of_not_ge (by simpa [Set.mem_Iic] using hx)
  have hevent : ∀ᵐ x ∂F, 0 ≤ 1 - Real.exp (-theta * x) ∧
        1 - Real.exp (-theta * x) ≤ 1 := by
    filter_upwards [hpos] with x hx
    have hneg : -theta * x ≤ 0 := by nlinarith
    have he : Real.exp (-theta * x) ≤ 1 := by
      calc
        Real.exp (-theta * x) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr hneg
        _ = 1 := Real.exp_zero
    constructor
    · linarith
    · linarith [Real.exp_pos (-theta * x)]
  have hint : Integrable (fun x : ℝ =>
      1 - Real.exp (-theta * x)) F := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hevent] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  calc
    (∫ x, (1 - Real.exp (-theta * x)) ∂F) ≤
        ∫ _x : ℝ, (1 : ℝ) ∂F :=
      integral_mono_ae hint (integrable_const 1)
        (hevent.mono (fun x hx => hx.2))
    _ = 1 := by simp

/-- Unit premium dominates the bounded jump contribution at large Laplace arguments. -/
theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    Tendsto (queueLaplaceExponent rate F) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [Filter.eventually_ge_atTop
    (max 0 (b + (rate : ℝ)))] with theta htheta
  have htheta0 : 0 ≤ theta :=
    (le_max_left (0 : ℝ) (b + (rate : ℝ))).trans htheta
  have hbound : (∫ x, (1 - Real.exp (-theta * x)) ∂F) ≤ 1 :=
    queueExpIntegralLeOne F hpositive theta htheta0
  have hrate0 : (0 : ℝ) ≤ rate := NNReal.coe_nonneg _
  have hm := mul_le_mul_of_nonneg_left hbound hrate0
  have hthetaB : b + (rate : ℝ) ≤ theta :=
    (le_max_right (0 : ℝ) (b + (rate : ℝ))).trans htheta
  dsimp [queueLaplaceExponent]
  linarith
