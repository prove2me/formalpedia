-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionStepSumCadlagNNRealV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:43:17.283277+00:00
-- url     : https://prove2.me/submissions/5206609e-4b46-4670-8c2a-84e691974465

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_isCadlag_stepIndicator
import Theorems.Thm_ProbabilityTheory_IsCadlag_add
import Theorems.Thm_ProbabilityTheory_isCadlag_const
import Theorems.Thm_isCadlag_comp_nnrealCoe

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    (s : Finset (ℝ × ℝ)) (weight : ℝ × ℝ → ℝ) :
    ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 =>
        ∑ p ∈ s, if p.1 ≤ (t : ℝ) then weight p else 0) := by
  classical
  have hreal (s : Finset (ℝ × ℝ)) : ProbabilityTheory.IsCadlag
      (fun t : ℝ => ∑ p ∈ s, if p.1 ≤ t then weight p else 0) := by
    induction s using Finset.induction with
    | empty =>
      simpa using
        (ProbabilityTheory.isCadlag_const (α := ℝ) (β := ℝ) (c := (0 : ℝ)))
    | @insert p s hp ih =>
      have hstep : ProbabilityTheory.IsCadlag
          (fun t : ℝ => if p.1 ≤ t then weight p else 0) :=
        ProbabilityTheory.isCadlag_stepIndicator
      simpa [Finset.sum_insert hp] using hstep.add ih
  exact isCadlag_comp_nnrealCoe (hreal s)
