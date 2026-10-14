-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.product_coeff_exp_bound_of_coordinate_coeff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T14:10:38.704996+00:00
-- url     : https://prove2.me/submissions/298f6674-020a-4a34-91c3-9631df76d85b

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

private lemma geometric_two_bound (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ j) ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ (2 : ℝ) ^ (k + 1) + 2 ^ (k + 1) := add_le_add ih le_rfl
      _ = 2 ^ (k + 1 + 1) := by rw [pow_succ]; ring

private lemma coeff_mul_bound (φ τ : PowerSeries ℂ) (M : ℕ)
    (hφ : ∀ k, ‖PowerSeries.coeff k φ‖ ≤ (2 : ℝ) ^ (k + M))
    (hτ : ∀ k, ‖PowerSeries.coeff k τ‖ ≤ 1) (k : ℕ) :
    ‖PowerSeries.coeff k (φ * τ)‖ ≤ (2 : ℝ) ^ (k + (M + 1)) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    ‖∑ j ∈ Finset.range (k + 1),
        PowerSeries.coeff j φ * PowerSeries.coeff (k - j) τ‖
        ≤ ∑ j ∈ Finset.range (k + 1),
          ‖PowerSeries.coeff j φ * PowerSeries.coeff (k - j) τ‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (j + M) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      calc
        ‖PowerSeries.coeff j φ‖ * ‖PowerSeries.coeff (k - j) τ‖
            ≤ ‖PowerSeries.coeff j φ‖ * 1 :=
          mul_le_mul_of_nonneg_left (hτ _) (norm_nonneg _)
        _ ≤ (2 : ℝ) ^ (j + M) := by simpa using hφ j
    _ = (∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ j) * 2 ^ M := by
      simp_rw [pow_add]
      rw [Finset.sum_mul]
    _ ≤ (2 : ℝ) ^ (k + 1) * 2 ^ M :=
      mul_le_mul_of_nonneg_right (geometric_two_bound k) (by positivity)
    _ = (2 : ℝ) ^ (k + (M + 1)) := by rw [← pow_add]; congr 1; omega

private lemma coeff_mul_pow_bound (φ τ : PowerSeries ℂ) (M m : ℕ)
    (hφ : ∀ k, ‖PowerSeries.coeff k φ‖ ≤ (2 : ℝ) ^ (k + M))
    (hτ : ∀ k, ‖PowerSeries.coeff k τ‖ ≤ 1) :
    ∀ k, ‖PowerSeries.coeff k (φ * τ ^ m)‖ ≤ (2 : ℝ) ^ (k + (M + m)) := by
  induction m with
  | zero => simpa using hφ
  | succ m ih =>
    intro k
    simpa [pow_succ, ← mul_assoc, Nat.add_assoc] using
      coeff_mul_bound (φ * τ ^ m) τ (M + m) ih hτ k

private lemma coeff_prod_pow_bound {σ : Type*} [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (m : σ → ℕ) (s : Finset σ)
    (hτ : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1) :
    ∀ k, ‖PowerSeries.coeff k (∏ i ∈ s, τ i ^ m i)‖ ≤
      (2 : ℝ) ^ (k + ∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro k
    by_cases hk : k = 0
    · subst k; simp
    · simp [PowerSeries.coeff_one, hk, pow_nonneg]
  | @insert i s hi ih =>
    intro k
    simpa [Finset.prod_insert hi, Finset.sum_insert hi, mul_comm,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coeff_mul_pow_bound (∏ j ∈ s, τ j ^ m j) (τ i) (∑ j ∈ s, m j) (m i)
        ih (hτ i) k

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (a β : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (H ws v : ℝ) (hws : 0 < ws) (hv : 0 < v)
    (hw : ∀ i, ws ≤ w i)
    (ha : MatrixTranslationBounds.weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v)
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1) :
    ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
      Real.exp (H * (Real.log 2 / v + Real.log 4 / ws)) := by
  have he : ∀ i, (e i).val ≤ a i := by
    intro i
    have hi := (e i).is_lt
    omega
  have hsum : ws * (∑ i, ((e i).val : ℝ)) ≤ H := by
    calc
      ws * (∑ i, ((e i).val : ℝ)) = ∑ i, ws * (e i).val := by rw [Finset.mul_sum]
      _ ≤ ∑ i, w i * (a i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          ws * (e i).val ≤ w i * (e i).val :=
            mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
          _ ≤ w i * (a i : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast he i) (le_trans hws.le (hw i))
      _ = MatrixTranslationBounds.weight w (fun i => a i) := by
        simp [MatrixTranslationBounds.weight]
      _ ≤ H := ha
  have hm : (∑ i, ((e i).val : ℝ)) ≤ H / ws := by
    rw [le_div_iff₀ hws]
    nlinarith [hsum]
  have hcoeff := coeff_prod_pow_bound τ (fun i => (e i).val) Finset.univ hτc k
  have hM : ((∑ i, (e i).val : ℕ) : ℝ) ≤ H / ws := by
    simpa using hm
  have hH : 0 ≤ H := by
    have h := (le_div_iff₀ hv).mp hk
    exact le_trans (mul_nonneg (Nat.cast_nonneg k) hv.le) h
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog24 : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have hexp : ((k + ∑ i, (e i).val : ℕ) : ℝ) * Real.log 2 ≤
      H * (Real.log 2 / v + Real.log 4 / ws) := by
    calc
      _ = (k : ℝ) * Real.log 2 + ((∑ i, (e i).val : ℕ) : ℝ) * Real.log 2 := by
        push_cast; ring
      _ ≤ (H / v) * Real.log 2 + (H / ws) * Real.log 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hk hlog2)
          (mul_le_mul_of_nonneg_right hM hlog2)
      _ ≤ (H / v) * Real.log 2 + (H / ws) * Real.log 4 := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ (2 : ℝ) ^ (k + ∑ i, (e i).val) := hcoeff
    _ = Real.exp (((k + ∑ i, (e i).val : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr hexp
