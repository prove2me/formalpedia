-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.rowScalar_exp_weight_difference_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:58:02.065925+00:00
-- url     : https://prove2.me/submissions/6f4b5f4c-e307-4e92-a7c4-2d988b44e9a0

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
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_factor_bound
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_binomial_factor_bound
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_epsilon_factor_bound

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (τ : σ → PowerSeries ℂ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν ws : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws)
    (hw : ∀ i, ws ≤ w i)
    (hcoeff : ‖PowerSeries.coeff k (∏ i, τ i ^ ((d i).val : ℕ))‖ ≤ (2 : ℝ) ^ k)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε τ β a d k‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        ν * weight w (fun i => (d i).val) +
        (C + Real.log 4) * weight w (fun i => a i) / ws +
        (k : ℝ) * Real.log 2) := by
  exact OAI.PiExponent.MatrixTranslationBounds.rowScalar_factor_bound
    ε τ β a d k w C ν ws hC hν hws hw
    (OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound
      β a d w ws hws hw)
    (OAI.PiExponent.MatrixTranslationBounds.rowScalar_epsilon_factor_bound
      ε β a d w C ν ws hC hν hws hw hε)
    hcoeff