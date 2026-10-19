-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_exp_bound_explicit_degree_weights
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:26:27.910689+00:00
-- url     : https://prove2.me/submissions/52177aaf-ac49-4ec2-928d-283bd3285b2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_bound_explicit_degree_weights_of_combinatorial_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_explicit_combinatorial_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction


theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (τ : σ → PowerSeries ℂ) (β a : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν : ℝ) (hC : 0 ≤ C)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i))
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1) :
    ‖RowTranslation.rowScalar ε τ β a e k‖ ≤
      Real.exp (-ν * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => β i)) +
        ν * MatrixTranslationBounds.weight w (fun i => (e i : ℕ)) +
        (Real.log 4 + C) * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ)) := by
  apply OAI.PiExponent.LiteralAnalytic.rowScalar_exp_bound_explicit_degree_weights_of_combinatorial_bound
      ε τ β a e k w C ν hC hε
  exact OAI.PiExponent.LiteralAnalytic.rowScalar_explicit_combinatorial_bound
      τ β a e k hτc

