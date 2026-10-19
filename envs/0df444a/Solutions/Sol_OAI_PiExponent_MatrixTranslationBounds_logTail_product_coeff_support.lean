-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.logTail_product_coeff_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:50:39.536329+00:00
-- url     : https://prove2.me/submissions/3cdbb5f5-8a54-4e76-b60b-63f6ec10cca7

import Mathlib
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

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation
theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (T e : σ → ℕ) (hT : ∀ i, 1 ≤ T i) (k : ℕ) :
    PowerSeries.coeff k
        (∏ i, (tail (T i) (PowerSeries.log ℂ)) ^ (e i)) ≠ 0 →
      (∑ i, T i * e i) ≤ k := by
  intro h
  by_contra hlt
  push Not at hlt
  have hdvd : ∀ i, (PowerSeries.X : PowerSeries ℂ) ^ (T i) ∣ tail (T i) (PowerSeries.log ℂ) := by
    intro i
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    unfold tail
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hn, sub_self]
  have hprod : (PowerSeries.X : PowerSeries ℂ) ^ (∑ i, T i * e i) ∣
      ∏ i, (tail (T i) (PowerSeries.log ℂ)) ^ (e i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_dvd_prod_of_dvd
    intro i _
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd (hdvd i) _
  exact h ((PowerSeries.X_pow_dvd_iff.mp hprod) k hlt)
