-- Prove2me | solution 2 for OAI.PiExponent.LiteralAnalytic.rowScalar_exp_bound_explicit_degree_weights_of_combinatorial_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:18:07.84825+00:00
-- url     : https://prove2.me/submissions/91164daa-3a2e-49f4-a07e-b2f7e5c67411

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
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (τ : σ → PowerSeries ℂ) (β a : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν : ℝ) (hC : 0 ≤ C)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i))
    (hComb :
      ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i) : ℕ) : ℝ) *
        ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
          Real.exp (Real.log 4 * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ))) :
    ‖RowTranslation.rowScalar ε τ β a e k‖ ≤
      Real.exp (-ν * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => β i)) +
        ν * MatrixTranslationBounds.weight w (fun i => (e i : ℕ)) +
        (Real.log 4 + C) * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ)) := by
  by_cases hβ : ∀ i, β i ≤ a i
  · have he : ∀ i, (e i : ℕ) ≤ a i - β i := fun i => Nat.lt_succ_iff.mp (e i).2
    have hcast : ∀ i, (((a i - β i - e i : ℕ)) : ℝ) = a i - β i - (e i : ℕ) := by
      intro i
      rw [Nat.cast_sub (he i), Nat.cast_sub (hβ i)]
    unfold RowTranslation.rowScalar
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_prod]
    set Cb : ℝ := ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i) : ℕ) : ℝ)
    set Q : ℝ := ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖
    have hprod : ∏ i, ‖ε i ^ (a i - β i - e i)‖ ≤
        Real.exp (∑ i, (C - ν * w i) * (((a i - β i - e i : ℕ)) : ℝ)) := by
      rw [Real.exp_sum]
      apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
      intro i _
      rw [norm_pow, mul_comm, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (hε i) _
    have hsum : ∑ i, (C - ν * w i) * (((a i - β i - e i : ℕ)) : ℝ) ≤
        -ν * (MatrixTranslationBounds.weight w (fun i => a i) -
          MatrixTranslationBounds.weight w (fun i => β i)) +
          ν * MatrixTranslationBounds.weight w (fun i => (e i : ℕ)) + C * ∑ i, (a i : ℝ) := by
      simp only [MatrixTranslationBounds.weight, hcast]
      have h1 : ∑ i, (C - ν * w i) * ((a i : ℝ) - β i - (e i : ℕ)) =
          -ν * (∑ i, w i * (a i : ℝ) - ∑ i, w i * (β i : ℝ)) + ν * ∑ i, w i * ((e i : ℕ) : ℝ)
            + C * ∑ i, ((a i : ℝ) - β i - (e i : ℕ)) := by
        trans ∑ i, (-ν * (w i * (a i : ℝ) - w i * (β i : ℝ)) + ν * (w i * ((e i : ℕ) : ℝ))
            + C * ((a i : ℝ) - β i - (e i : ℕ)))
        · exact Finset.sum_congr rfl fun i _ => by ring
        · simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [h1]
      have h2 : C * ∑ i, ((a i : ℝ) - β i - (e i : ℕ)) ≤ C * ∑ i, (a i : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.sum_le_sum
        intro i _
        have : (0 : ℝ) ≤ β i := Nat.cast_nonneg _
        have : (0 : ℝ) ≤ ((e i : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    have hCb : 0 ≤ Cb := Nat.cast_nonneg _
    calc (Cb * ∏ i, ‖ε i ^ (a i - β i - e i)‖) * Q
        = (Cb * Q) * ∏ i, ‖ε i ^ (a i - β i - e i)‖ := by ring
      _ ≤ Real.exp (Real.log 4 * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ)) *
          Real.exp (∑ i, (C - ν * w i) * (((a i - β i - e i : ℕ)) : ℝ)) :=
          mul_le_mul hComb hprod (Finset.prod_nonneg fun i _ => norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((Real.log 4 * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ)) +
          ∑ i, (C - ν * w i) * (((a i - β i - e i : ℕ)) : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · push Not at hβ
    obtain ⟨i, hi⟩ := hβ
    have h0 : (∏ j, (a j).choose (β j) * (a j - β j).choose (e j) : ℕ) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Nat.choose_eq_zero_of_lt hi, zero_mul]
    unfold RowTranslation.rowScalar
    rw [h0]
    simp only [Nat.cast_zero, zero_mul, norm_zero]
    exact (Real.exp_pos _).le
