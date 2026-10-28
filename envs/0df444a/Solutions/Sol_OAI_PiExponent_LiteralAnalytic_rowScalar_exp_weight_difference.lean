-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T13:34:58.459552+00:00
-- url     : https://prove2.me/submissions/95fda2ce-4101-4b2d-b13b-a9818de58d89

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
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_weight_difference_of_coeff_bounds
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_log_tail_coeff_bounds

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i)
    (ha : MatrixTranslationBounds.weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖RowTranslation.rowScalar ε (fun i => RowTranslation.tail (T i) (PowerSeries.log ℂ)) β a e k‖ ≤
      Real.exp (-ν * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  apply OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_coeff_bounds
      ε (fun i => RowTranslation.tail (T i) (PowerSeries.log ℂ)) T β a e k w C ν H ws v F
      hC hν hws hv hF hw ha hk hT hTw hε
  · intro i n
    exact (OAI.PiExponent.LiteralAnalytic.log_tail_coeff_bounds (T i) n).1
  · intro i n hn
    exact (OAI.PiExponent.LiteralAnalytic.log_tail_coeff_bounds (T i) n).2 hn
