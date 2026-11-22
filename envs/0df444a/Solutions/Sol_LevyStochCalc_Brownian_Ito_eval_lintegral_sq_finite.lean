-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.eval_lintegral_sq_finite
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:51:39.727459+00:00
-- url     : https://prove2.me/submissions/40782f85-228e-4152-a623-e04e1b0aef46

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: `L¹`/`L²` convergence and adapted approximation

Transfer of the martingale property along `L¹`-limits, criteria for `L¹`
convergence of squares from `L²` bounds, the endpoint `L²` bound for differences of
simple integrals, and the existence of an adapted `SimplePredictable` integrand
within a prescribed `L²([0, T] × Ω)` tolerance of a progressively measurable
square-integrable integrand, together with the norm and increment identities they
use.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]



theorem _root_.solution
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {T' : ℝ} (H : SimplePredictable Ω T') (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  classical
  choose C hC using H.ξ_bounded
  let B : ℝ≥0 := ⟨∑ i : Fin H.N, |C i|, Finset.sum_nonneg fun i _ => abs_nonneg (C i)⟩
  have hbound (ω : Ω) (s : ℝ) : ‖H.eval s ω‖₊ ≤ B := by
    change (‖H.eval s ω‖₊ : ℝ) ≤ ∑ i : Fin H.N, |C i|
    simp only [coe_nnnorm, Real.norm_eq_abs, SimplePredictable.eval]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    split
    · exact (hC i ω).trans (le_abs_self _)
    · simpa using abs_nonneg (C i)
  calc
    _ ≤ ∫⁻ _ : Ω, ∫⁻ _ in Set.Icc (0 : ℝ) T, (B : ℝ≥0∞)^2 ∂volume ∂P := by
      apply lintegral_mono
      intro ω
      apply lintegral_mono
      intro s
      exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr (hbound ω s)) 2
    _ < ⊤ := by
      rw [lintegral_const, lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
      simp only [measure_univ, mul_one]
      exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
