-- Prove2me | solution 1 for Kyprianou.Ch01.integerCompoundPoissonPathMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:59:58.165652+00:00
-- url     : https://prove2.me/submissions/b793174c-5ed7-484f-9e5f-a4313f5f21ea

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonFixedTimeMeasurable
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every deterministic-time section is measurable, hence so is the
unstopped integer-valued compound Poisson path in the product σ-algebra. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (hArrival : ∀ n, Measurable (arrival n))
    (hMarks : ∀ n, Measurable (marks n)) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      integerCompoundPoisson y arrival marks t ω) := by
  apply measurable_pi_iff.2
  intro t
  exact Kyprianou.Ch01.integerCompoundPoissonFixedTimeMeasurable
    y arrival marks hArrival hMarks t
