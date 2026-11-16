-- Prove2me | solution 1 for Kyprianou.Ch01.queueLaplaceExponent_strictConvex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T11:22:40.070206+00:00
-- url     : https://prove2.me/submissions/0244d864-c3db-40e9-aa7f-35c222b9b0ae

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_queueNegIntegratedExp_strictConvex

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Linear premium plus positive multiple of a strictly convex claim transform. -/
theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    StrictConvexOn ℝ (Set.Ici (0 : ℝ))
      (queueLaplaceExponent rate F) := by
  have hs := Kyprianou.Ch01.queueNegIntegratedExp_strictConvex F hpositive
  refine ⟨convex_Ici (0 : ℝ), ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have h := hs.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  dsimp only [queueLaplaceExponent] at *
  have hr : (0 : ℝ) < (rate : ℝ) := by exact_mod_cast hrate
  have hgap :
      0 < -(a * (∫ z : ℝ, (1 - Real.exp (-x * z)) ∂F)) -
          b * (∫ z : ℝ, (1 - Real.exp (-y * z)) ∂F) +
          (∫ z : ℝ, (1 - Real.exp (-(a * x + b * y) * z)) ∂F) := by
    linarith
  have hp := mul_pos hr hgap
  nlinarith
