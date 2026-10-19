-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound_weight_exp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:24:26.705177+00:00
-- url     : https://prove2.me/submissions/dc4d8e76-6e21-4382-bad2-873f0c826256

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

/-!
Weighted binomial exponential comparison.
The coordinatewise lower bound on weights implies a bound on the
unweighted coordinate sum. The exact exponential power identity avoids
an induction simplification ambiguity in the previous compiler failure.
-/
theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (a : σ →₀ ℕ) (w : σ → ℝ) (ws : ℝ)
    (hws : 0 < ws) (hw : ∀ i, ws ≤ w i) :
    (4 : ℝ) ^ (∑ i, a i) ≤
      Real.exp (Real.log 4 * weight w (fun i => a i) / ws) := by
  have hsum : (∑ i, (a i : ℝ)) ≤ weight w (fun i => a i) / ws := by
    apply (le_div_iff₀ hws).2
    calc
      (∑ i, (a i : ℝ)) * ws = ∑ i, (a i : ℝ) * ws := by
        rw [Finset.sum_mul]
      _ ≤ ∑ i, (a i : ℝ) * w i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hw i) (Nat.cast_nonneg (a i))
      _ = weight w (fun i => a i) := by
        rw [weight]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hpow (n : ℕ) :
      (4 : ℝ) ^ n = Real.exp (Real.log 4 * (n : ℝ)) := by
    calc
      (4 : ℝ) ^ n = (Real.exp (Real.log 4)) ^ n := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ = Real.exp ((n : ℝ) * Real.log 4) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (Real.log 4 * (n : ℝ)) := by
        ring
  rw [hpow (∑ i, a i)]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log 4 :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  have hscaled := mul_le_mul_of_nonneg_left hsum hlog
  simpa only [Nat.cast_sum, ← mul_div_assoc] using hscaled
