-- Prove2me | solution 1 for KellyLossNetworks.Routing.mean_Z_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:11:24.177944+00:00
-- url     : https://prove2.me/submissions/b9244de3-29ca-4385-b6dc-087a7ec458d4

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

open KellyLossNetworks.Routing in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (C : ℝ) (hint : Integrable (fun t => max (t - C) 0) μ)
    (h446 : 2 * excessMean μ C < spareMean μ C) :
    (∀ ε : ℝ, 0 < ε → ε < spareMean μ C ^ 2 →
      ∫ p, Zv μ C ε p ∂(μ.prod μ) =
        2 * excessMean μ C * spareMean μ C / (spareMean μ C ^ 2 - ε)) ∧
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ spareMean μ C ^ 2 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∫ p, Zv μ C ε p ∂(μ.prod μ) < 1 := by
  have hE0 : 0 ≤ excessMean μ C := integral_nonneg (fun t => le_max_right _ _)
  have hintS : Integrable (fun t => max (C - t) 0) μ := by
    refine Integrable.mono' (integrable_const (max C 0))
      ((continuous_const.sub continuous_id).max continuous_const).aestronglyMeasurable ?_
    filter_upwards [hnonneg] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (by linarith) le_rfl
  have hi1 : Integrable (fun p : ℝ × ℝ => max (p.1 - C) 0 * max (C - p.2) 0) (μ.prod μ) :=
    hint.mul_prod hintS
  have h2 : (fun p : ℝ × ℝ => max (p.2 - C) 0 * max (C - p.1) 0) =
      fun p => max (C - p.1) 0 * max (p.2 - C) 0 := by
    funext p; ring
  have hi2 : Integrable (fun p : ℝ × ℝ => max (p.2 - C) 0 * max (C - p.1) 0) (μ.prod μ) := by
    rw [h2]; exact hintS.mul_prod hint
  have I1 : ∫ p, max (p.1 - C) 0 * max (C - p.2) 0 ∂(μ.prod μ) =
      excessMean μ C * spareMean μ C :=
    integral_prod_mul (fun t => max (t - C) 0) (fun t => max (C - t) 0)
  have I2 : ∫ p, max (p.2 - C) 0 * max (C - p.1) 0 ∂(μ.prod μ) =
      spareMean μ C * excessMean μ C := by
    rw [h2]
    exact integral_prod_mul (fun t => max (C - t) 0) (fun t => max (t - C) 0)
  have part1 : ∀ ε : ℝ, ∫ p, Zv μ C ε p ∂(μ.prod μ) =
      2 * excessMean μ C * spareMean μ C / (spareMean μ C ^ 2 - ε) := by
    intro ε
    unfold Zv
    rw [integral_div, integral_add hi1 hi2, I1, I2]
    ring
  refine ⟨fun ε _ _ => part1 ε, ?_⟩
  set E := excessMean μ C
  set S := spareMean μ C
  have hS : 0 < S := by linarith
  refine ⟨S * (S - 2 * E), mul_pos hS (by linarith), by nlinarith, fun ε h1 h2 => ?_⟩
  rw [part1 ε, div_lt_one (by nlinarith)]
  nlinarith
