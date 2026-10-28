-- Prove2me | solution 1 for Measurable.dotProduct_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:21.243379+00:00
-- url     : https://prove2.me/submissions/83ce8f78-6004-4017-a1de-425355e476b6

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

-- carved verbatim out of submission 028e111f-382d-40d0-8008-127228d5e6cf, lines 612-620


open MeasureTheory ProbabilityTheory Matrix NNReal in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {M : Ω → Matrix (Fin d) (Fin d) ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j)
    {v w : Ω → Fin d → ℝ} (hv : Measurable v) (hw : Measurable w) :
    Measurable fun ω => v ω ⬝ᵥ M ω *ᵥ w ω := by
  simp only [dotProduct, mulVec]
  refine Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hv).mul ?_
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul ((measurable_pi_apply j).comp hw)
