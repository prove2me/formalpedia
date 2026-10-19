-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.rowScalar_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:37:20.234825+00:00
-- url     : https://prove2.me/submissions/75f2c6f9-3c79-4391-8160-4c6bd33cae61

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
Combine the three supplied norm bounds for the rowScalar product.
The exact exponential natural-multiple identity avoids the unsolved
successor step in the earlier remote candidate.
-/
theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (τ : σ → PowerSeries ℂ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν ws : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws)
    (hw : ∀ i, ws ≤ w i)
    (hbin : ‖((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : ℂ)‖ ≤
      Real.exp (Real.log 4 * weight w (fun i => a i) / ws))
    (heps : ‖∏ i, ε i ^ (a i - β i - d i)‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        ν * weight w (fun i => (d i).val) +
        C * weight w (fun i => a i) / ws))
    (hcoeff : ‖PowerSeries.coeff k (∏ i, τ i ^ ((d i).val : ℕ))‖ ≤ (2 : ℝ) ^ k) :
    ‖rowScalar ε τ β a d k‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        ν * weight w (fun i => (d i).val) +
        (C + Real.log 4) * weight w (fun i => a i) / ws +
        (k : ℝ) * Real.log 2) := by
  have hpow (n : ℕ) :
      (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ n = (Real.exp (Real.log 2)) ^ n := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((n : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul]
  calc
    ‖rowScalar ε τ β a d k‖ ≤
        Real.exp (Real.log 4 * weight w (fun i => a i) / ws) *
          Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
            ν * weight w (fun i => (d i).val) +
            C * weight w (fun i => a i) / ws) * (2 : ℝ) ^ k := by
      rw [rowScalar, norm_mul, norm_mul]
      exact mul_le_mul
        (mul_le_mul hbin heps (norm_nonneg _) (Real.exp_nonneg _))
        hcoeff
        (norm_nonneg _)
        (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = Real.exp (Real.log 4 * weight w (fun i => a i) / ws +
          (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
            ν * weight w (fun i => (d i).val) +
            C * weight w (fun i => a i) / ws) +
          (k : ℝ) * Real.log 2) := by
      rw [hpow]
      simp only [← Real.exp_add]
      all_goals (congr 1 <;> ring)
    _ = Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
          ν * weight w (fun i => (d i).val) +
          (C + Real.log 4) * weight w (fun i => a i) / ws +
          (k : ℝ) * Real.log 2) := by
      congr 1
      ring
