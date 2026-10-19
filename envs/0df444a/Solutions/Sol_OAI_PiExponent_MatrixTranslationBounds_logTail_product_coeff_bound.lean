-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.logTail_product_coeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:58:50.535533+00:00
-- url     : https://prove2.me/submissions/87eee320-a6c8-4cb6-8dc5-828ddb1bf7fa

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
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_pow_bound_of_zero_constant
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_logTail_coeff_bounds

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem solution {σ : Type*} [Fintype σ] [DecidableEq σ]
    (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) :
    ‖PowerSeries.coeff k
        (∏ i, (tail (T i) (PowerSeries.log ℂ)) ^ ((d i).val : ℕ))‖ ≤ (2 : ℝ) ^ k := by
  apply OAI.PiExponent.MatrixTranslationBounds.coeff_prod_pow_bound_of_zero_constant
    (f := fun i => tail (T i) (PowerSeries.log ℂ))
    (m := fun i => (d i).val) k
  · intro i
    exact (OAI.PiExponent.MatrixTranslationBounds.logTail_coeff_bounds (T i)).1
  · intro i n
    exact (OAI.PiExponent.MatrixTranslationBounds.logTail_coeff_bounds (T i)).2 n