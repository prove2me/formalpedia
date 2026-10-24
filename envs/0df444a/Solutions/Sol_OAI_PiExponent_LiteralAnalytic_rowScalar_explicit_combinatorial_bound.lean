-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_explicit_combinatorial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:50:08.828362+00:00
-- url     : https://prove2.me/submissions/ef534b54-8458-4cd4-854c-f8a15666432f

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_coefficient_composition_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_weighted_binomial_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (β a : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ)
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1) :
    ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i) : ℕ) : ℝ) *
      ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
        Real.exp (Real.log 4 * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ)) := by
  let P : ℝ := ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i) : ℕ) : ℝ)
  let E : ℕ := ∑ i, (e i : ℕ)
  have hB : P * (2 : ℝ) ^ E ≤ Real.exp (Real.log 4 * (∑ i, (a i : ℝ))) := by
    simpa [P, E] using
      OAI.PiExponent.LiteralAnalytic.rowScalar_weighted_binomial_bound a β e
  have hC : ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
      Real.exp (Real.log 2 * (k : ℝ)) * (2 : ℝ) ^ E := by
    simpa [E] using
      OAI.PiExponent.LiteralAnalytic.rowScalar_coefficient_composition_bound
        τ (fun i => (e i : ℕ)) k hτc
  change P * ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
    Real.exp (Real.log 4 * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ))
  calc
    P * ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
        P * (Real.exp (Real.log 2 * (k : ℝ)) * (2 : ℝ) ^ E) :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    _ = (P * (2 : ℝ) ^ E) * Real.exp (Real.log 2 * (k : ℝ)) := by ring
    _ ≤ Real.exp (Real.log 4 * (∑ i, (a i : ℝ))) *
        Real.exp (Real.log 2 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
    _ = Real.exp (Real.log 4 * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ)) := by
      rw [← Real.exp_add]