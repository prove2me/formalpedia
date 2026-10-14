-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound_support_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T14:45:45.311542+00:00
-- url     : https://prove2.me/submissions/4906cb6e-1030-471d-b4c9-0f7a9387bf67

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

theorem solution
    {s : Type*} [Fintype s] [DecidableEq s]
    (tau : s -> PowerSeries Complex) (beta a : Finsupp s Nat)
    (e : forall i, Fin (a i - beta i + 1)) (k : Nat) (w : s -> Real)
    (H v F : Real) (hv : 0 < v) (hF : 0 < F)
    (hk : (k : Real) <= H / v) (T : s -> Nat)
    (hT : forall i, 1 <= T i)
    (hTw : forall i, F * w i <= v * T i)
    (htaus : forall i n, n < T i -> PowerSeries.coeff n (tau i) = 0)
    (hcoeff : Not (PowerSeries.coeff k (Finset.univ.prod fun i => tau i ^ (e i).val) = 0)) :
    (Finset.univ.sum fun i => w i * (((e i).val : Nat) : Real)) <= H / F := by
  classical
  have hlow : forall i, (T i : ENat) <= PowerSeries.order (tau i) := by
    intro i
    apply PowerSeries.nat_le_order
    intro n hn
    exact htaus i n hn
  have cast_mul_smul : forall m n : Nat, ((m * n : Nat) : ENat) = m • (n : ENat) := by
    intro m n
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.succ_mul, Nat.cast_add, ih, succ_nsmul]
  have hpow : forall i, ((e i).val * T i : ENat) <=
      PowerSeries.order (tau i ^ (e i).val) := by
    intro i
    calc
      ((e i).val : ENat) * (T i : ENat) =
          (e i).val • (T i : ENat) := by simp [nsmul_eq_mul]
      _ <= (e i).val • PowerSeries.order (tau i) := nsmul_le_nsmul_right (hlow i) _
      _ <= PowerSeries.order (tau i ^ (e i).val) := PowerSeries.le_order_pow (tau i) (e i).val
  have hsum : (Finset.univ.sum fun i : s => (e i).val * T i) <= k := by
    have hsumOrd : (Finset.univ.sum fun i : s => ((e i).val * T i : ENat)) <=
        PowerSeries.order (Finset.univ.prod fun i => tau i ^ (e i).val) := by
      calc
        (Finset.univ.sum fun i : s => ((e i).val * T i : ENat)) <=
            Finset.univ.sum fun i : s => PowerSeries.order (tau i ^ (e i).val) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hpow i
        _ <= PowerSeries.order (Finset.univ.prod fun i => tau i ^ (e i).val) := by
          simpa using PowerSeries.le_order_prod (fun i => tau i ^ (e i).val) Finset.univ
    have hkOrd := PowerSeries.order_le k hcoeff
    have hcast : (Finset.univ.sum fun i : s => ((e i).val * T i : ENat)) <= (k : ENat) :=
      hsumOrd.trans hkOrd
    exact_mod_cast hcast
  have hreal : (Finset.univ.sum fun i : s => (((e i).val * T i : Nat) : Real)) <= (k : Real) := by
    exact_mod_cast hsum
  have hmul : F * (Finset.univ.sum fun i : s => w i * (((e i).val : Nat) : Real)) <=
      v * (Finset.univ.sum fun i : s => ((T i : Nat) : Real) * (((e i).val : Nat) : Real)) := by
    calc
      F * (Finset.univ.sum fun i : s => w i * (((e i).val : Nat) : Real)) =
          Finset.univ.sum fun i : s => (F * w i) * (((e i).val : Nat) : Real) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ <= Finset.univ.sum fun i : s => (v * ((T i : Nat) : Real)) * (((e i).val : Nat) : Real) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hTw i) (Nat.cast_nonneg _)
      _ = v * (Finset.univ.sum fun i : s => ((T i : Nat) : Real) * (((e i).val : Nat) : Real)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hright : v * (Finset.univ.sum fun i : s => ((T i : Nat) : Real) * (((e i).val : Nat) : Real)) <= H := by
    have heq : (Finset.univ.sum fun i : s => ((T i : Nat) : Real) * (((e i).val : Nat) : Real)) =
        Finset.univ.sum fun i : s => (((e i).val * T i : Nat) : Real) := by
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      ring
    rw [heq]
    have hk' : (k : Real) * v <= H := (le_div_iff₀ hv).mp hk
    nlinarith [mul_le_mul_of_nonneg_left hreal (le_of_lt hv)]
  have hfinal : F * (Finset.univ.sum fun i : s => w i * (((e i).val : Nat) : Real)) <= H := hmul.trans hright
  exact (le_div_iff₀ hF).2 (by nlinarith)
