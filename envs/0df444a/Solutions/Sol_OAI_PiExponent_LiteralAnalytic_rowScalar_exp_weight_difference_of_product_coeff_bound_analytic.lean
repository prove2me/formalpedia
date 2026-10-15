-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound_analytic
-- status  : ACCEPTED   (disprove)
-- author  : @queelius
-- created : 2026-10-15T05:35:58.112259+00:00
-- url     : https://prove2.me/submissions/85aecf5a-9d3d-4cba-b627-7d7bb932dd8c

-- Counterexample from Eyal1990 submission 4cd25fc0-a72c-4618-a755-b755b2455d7d.
-- Universe zero is explicit to avoid unresolved universe metavariables in the verifier.
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
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction


theorem solution : ¬ (∀ {s : Type 0} [Fintype s] [DecidableEq s]
    (eps : s -> Complex) (tau : s -> PowerSeries Complex) (beta a : Finsupp s Nat)
    (e : forall i, Fin (a i - beta i + 1)) (k : Nat) (w : s -> Real)
    (C nu H ws v F : Real) (hC : 0 <= C) (hnu : 0 <= nu)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : forall i, ws <= w i)
    (ha : MatrixTranslationBounds.weight w (fun i => a i) <= H)
    (hd : (Finset.univ.sum fun i => w i * (((e i).val : Nat) : Real)) <= H / F)
    (heps : forall i, ‖eps i‖ <= Real.exp (C - nu * w i))
    (hprod : ‖PowerSeries.coeff k (Finset.univ.prod fun i => tau i ^ (e i).val)‖ <=
      Real.exp (H * (Real.log 2 / v + Real.log 4 / ws))),
    ‖RowTranslation.rowScalar eps tau beta a e k‖ <=
      Real.exp (-nu * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => beta i)) +
        H * (nu / F + Real.log 2 / v + (Real.log 4 + C) / ws))) := by
  intro h
  let R : Real := 64
  let a : Finsupp PUnit Nat := Finsupp.single PUnit.unit 2
  let beta : Finsupp PUnit Nat := Finsupp.single PUnit.unit 1
  let eps : PUnit -> Complex := fun _ => 1
  let tau : PUnit -> PowerSeries Complex := fun _ => PowerSeries.C (Complex.ofReal R)
  let e : forall i : PUnit, Fin (a i - beta i + 1) := fun _ => ⟨1, by norm_num [a, beta]⟩
  let w : PUnit -> Real := fun _ => 1
  have h64 : Real.exp (2 * (Real.log 2 + Real.log 4)) = 64 := by
    have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
    have h4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
    rw [show 2 * (Real.log 2 + Real.log 4) =
      Real.log 2 + Real.log 2 + Real.log 4 + Real.log 4 by ring]
    simp only [Real.exp_add, h2, h4]
    norm_num
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hcoef : PowerSeries.coeff 0 (Finset.univ.prod fun i : PUnit => tau i ^ (e i).val) =
      Complex.ofReal R := by
    simp [tau, e]
  have hNorm : ‖(Complex.ofReal R)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hExp : Real.exp (2 * (Real.log 2 / 1 + Real.log 4 / 1)) = 64 := by
    rw [div_one, div_one]
    exact h64
  have hprod : ‖PowerSeries.coeff 0 (Finset.univ.prod fun i : PUnit => tau i ^ (e i).val)‖ <=
      Real.exp (2 * (Real.log 2 / 1 + Real.log 4 / 1)) := by
    rw [hcoef, hNorm, hExp]
  have hrow : ‖RowTranslation.rowScalar eps tau beta a e 0‖ = 128 := by
    simp [RowTranslation.rowScalar, eps, tau, e, a, beta, R, Complex.norm_real]
    norm_num
  have hbound := @h (PUnit : Type 0) inferInstance inferInstance eps tau beta a e 0 w 0 0 2 1 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro i; norm_num [w])
    (by simp [MatrixTranslationBounds.weight, a, w])
    (by simp [e, w])
    (by intro i; simp [eps, w])
    hprod
  rw [hrow] at hbound
  have hrhs : Real.exp (-(0 : Real) *
      (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => beta i)) +
        2 * ((0 : Real) / 2 + Real.log 2 / 1 + (Real.log 4 + 0) / 1)) = R := by
    rw [div_one, div_one]
    have hexp : -(0 : Real) *
        (MatrixTranslationBounds.weight w (fun i => a i) -
          MatrixTranslationBounds.weight w (fun i => beta i)) +
          2 * ((0 : Real) / 2 + Real.log 2 + (Real.log 4 + 0)) =
        2 * (Real.log 2 + Real.log 4) := by ring
    rw [hexp, h64]
  rw [hrhs] at hbound
  norm_num at hbound
