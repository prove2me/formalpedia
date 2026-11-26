-- Prove2me | solution 1 for MeasureTheory.Martingale.square_sub_pathwiseQuadraticVariation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:33:21.784904+00:00
-- url     : https://prove2.me/submissions/46a7c956-4339-4a68-8f6b-5859d5135abc

import Definitions.Def_SourceProof_549506abde5375992c159de2

open MeasureTheory
open scoped BigOperators ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem solution
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ) :
    Martingale (squareMinusPathwiseQuadraticVariation M) 𝓕 μ := by
  exact Prove2MeSourceProof.h_549506abde5375992c159de2 hM hM_two
