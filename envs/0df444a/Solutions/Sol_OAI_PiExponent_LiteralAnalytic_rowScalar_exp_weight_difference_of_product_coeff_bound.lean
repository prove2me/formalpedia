-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T14:20:54.108154+00:00
-- url     : https://prove2.me/submissions/2313af99-3db7-42f5-8cc4-861217c527eb
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

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_weight_difference_of_product_coeff_bound_support_weight
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_weight_difference_of_product_coeff_bound_analytic

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution
    {s : Type*} [Fintype s] [DecidableEq s]
    (eps : s -> Complex) (tau : s -> PowerSeries Complex) (beta a : Finsupp s Nat)
    (e : forall i, Fin (a i - beta i + 1)) (k : Nat) (w : s -> Real)
    (C nu H ws v F : Real) (hC : 0 <= C) (hnu : 0 <= nu)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : forall i, ws <= w i)
    (ha : MatrixTranslationBounds.weight w (fun i => a i) <= H)
    (hk : (k : Real) <= H / v) (T : s -> Nat)
    (hT : forall i, 1 <= T i)
    (hTw : forall i, F * w i <= v * T i)
    (htaus : forall i n, n < T i -> PowerSeries.coeff n (tau i) = 0)
    (heps : forall i, ‖eps i‖ <= Real.exp (C - nu * w i))
    (hprod : ‖PowerSeries.coeff k (Finset.univ.prod fun i => tau i ^ (e i).val)‖ <=
      Real.exp (H * (Real.log 2 / v + Real.log 4 / ws))) :
    ‖RowTranslation.rowScalar eps tau beta a e k‖ <=
      Real.exp (-nu * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => beta i)) +
        H * (nu / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  classical
  by_cases hc : PowerSeries.coeff k (Finset.univ.prod fun i => tau i ^ (e i).val) = 0
  · unfold RowTranslation.rowScalar
    simp [hc]
    exact le_of_lt (Real.exp_pos _)
  · have hd :=
      OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound_support_weight
        tau beta a e k w H v F hv hF hk T hT hTw htaus hc
    exact OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound_analytic
      eps tau beta a e k w C nu H ws v F hC hnu hws hv hF hw ha hd heps hprod
