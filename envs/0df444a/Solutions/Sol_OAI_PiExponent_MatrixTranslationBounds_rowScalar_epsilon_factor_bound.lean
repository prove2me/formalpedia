-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.rowScalar_epsilon_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:16:13.36758+00:00
-- url     : https://prove2.me/submissions/e4bedfd7-ab8b-4546-a1b9-1e878fa92a4d

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
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_epsilon_product_exp_bound
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_epsilon_exponent_weight_bound

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ)
    (C ν ws : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws)
    (hw : ∀ i, ws ≤ w i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖∏ i, ε i ^ (a i - β i - d i)‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        ν * weight w (fun i => (d i).val) +
        C * weight w (fun i => a i) / ws) := by
  have hprod := OAI.PiExponent.MatrixTranslationBounds.epsilon_product_exp_bound
    ε β a d w C ν hε
  have hexp := OAI.PiExponent.MatrixTranslationBounds.epsilon_exponent_weight_bound
    β a d w C ν ws hC hν hws hw
  exact le_trans hprod (Real.exp_le_exp.mpr hexp)