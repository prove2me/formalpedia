-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.norm_rowScalar_exp_weight_difference
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:35:20.53928+00:00
-- url     : https://prove2.me/submissions/e58f91d3-d63b-4e7b-a276-6db1937ba455

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
import Definitions.Def_OAI_PiExponent_LiteralAnalytic_choiceScalarMajorant
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_logTail_product_coeff_controls
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_exp_weight_difference_of_controls

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem solution {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (ha : weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws) ) := by
  classical
  have hctrl := OAI.PiExponent.MatrixTranslationBounds.logTail_product_coeff_controls
    T β a d k w H v F hv hF hT hk hTw
  by_cases hz : PowerSeries.coeff k
      (∏ i, (tail (T i) (PowerSeries.log ℂ)) ^ ((d i).val : ℕ)) = 0
  · rw [rowScalar, hz, mul_zero, norm_zero]
    exact (Real.exp_pos _).le
  · exact OAI.PiExponent.MatrixTranslationBounds.rowScalar_exp_weight_difference_of_controls
      ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k w C ν H ws v F
      hC hν hws hv hF hw ha hk hctrl.1 (hctrl.2 hz) hε
