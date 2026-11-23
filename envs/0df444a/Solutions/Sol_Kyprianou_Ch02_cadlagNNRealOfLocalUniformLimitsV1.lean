-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagNNRealOfLocalUniformLimitsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:07:41.204799+00:00
-- url     : https://prove2.me/submissions/abe7fcc7-0d0f-482e-b408-072d781ee799

import Theorems.Thm_Kyprianou_Ch02_cadlagNNRealUniformLimitRightContinuousV1
import Theorems.Thm_Kyprianou_Ch02_cadlagNNRealUniformLimitLeftLimitsV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open Filter Set Topology ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02
theorem solution
    (f : ℝ≥0 → ℝ)
    (happrox : ∀ T : ℝ≥0, 0 < T →
      ∃ (F : ℕ → ℝ≥0 → ℝ),
        (∀ n, ProbabilityTheory.IsCadlag (F n)) ∧
        ∀ δ : ℝ, 0 < δ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : ℝ≥0, t ≤ T →
            |F n t - f t| < δ) :
    ProbabilityTheory.IsCadlag f
    := by
  intro t
  constructor
  · exact Kyprianou.Ch02.cadlagNNRealUniformLimitRightContinuousV1 f happrox t
  · exact Kyprianou.Ch02.cadlagNNRealUniformLimitLeftLimitsV1 f happrox t

