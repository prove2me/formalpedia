-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:07:11.199337+00:00
-- url     : https://prove2.me/submissions/d21dd4b0-274c-4c53-b1e2-9d4de647b8aa

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
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_binomial_factor_bound_nat_majorant
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_binomial_factor_bound_weight_exp

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ) (ws : ℝ)
    (hws : 0 < ws) (hw : ∀ i, ws ≤ w i) :
    ‖((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : ℂ)‖ ≤
      Real.exp (Real.log 4 * weight w (fun i => a i) / ws) := by
  exact le_trans
    (OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound_nat_majorant
      β a d)
    (OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound_weight_exp
      a w ws hws hw)
