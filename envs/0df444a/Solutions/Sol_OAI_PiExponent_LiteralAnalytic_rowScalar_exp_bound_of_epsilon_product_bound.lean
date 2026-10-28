-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_exp_bound_of_epsilon_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:19:56.338481+00:00
-- url     : https://prove2.me/submissions/23e5a815-f344-4721-8d78-d7a5bc11fd2c

import Mathlib
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
    (C ν : ℝ)
    (hEpsProd :
      ‖∏ i, ε i ^ (a i - β i - (e i : ℕ))‖ ≤
        Real.exp (C * (∑ i, (a i : ℝ)) - ν *
          (MatrixTranslationBounds.weight w (fun i => a i) -
            MatrixTranslationBounds.weight w (fun i => β i)) +
          ν * MatrixTranslationBounds.weight w (fun i => (e i : ℕ))))
    (hComb :
      ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i) : ℕ) : ℝ) *
        ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
          Real.exp (Real.log 4 * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ))) :
    ‖RowTranslation.rowScalar ε τ β a e k‖ ≤
      Real.exp (-ν * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => β i)) +
        ν * MatrixTranslationBounds.weight w (fun i => (e i : ℕ)) +
        (Real.log 4 + C) * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ)) := by
  rw [RowTranslation.rowScalar, norm_mul, norm_mul, Complex.norm_natCast]
  have h := mul_le_mul hComb hEpsProd (norm_nonneg _) (Real.exp_pos _).le
  rw [← Real.exp_add] at h
  calc _ = ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i) : ℕ) : ℝ) *
        ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ * ‖∏ i, ε i ^ (a i - β i - (e i : ℕ))‖ := by ring
    _ ≤ _ := h
    _ = _ := by congr 1; ring
