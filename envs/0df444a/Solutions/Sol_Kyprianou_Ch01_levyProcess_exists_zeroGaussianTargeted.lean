-- Prove2me | solution 1 for Kyprianou.Ch01.levyProcess_exists_zeroGaussianTargeted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T19:51:33.244372+00:00
-- url     : https://prove2.me/submissions/6af4b088-2a50-4557-8f4c-aa3b85794c09

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Theorems.Thm_ProbabilityTheory_exists_isLevyProcess_pureJump
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_def
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hzero : T.gaussianVariance = 0) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧
        (∀ t, Measurable (X t)) ∧
        ∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (μ.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              Kyprianou.Ch01.levyTripleExponent T ξ) := by   classical
  let b : ℝ := T.drift
  let nu : Measure ℝ := T.levyMeasure
  have hnu : ProbabilityTheory.IsLevyMeasure nu := by
    exact T.levyMeasure_isLevyMeasure
  obtain ⟨Ω, m, μ, X, hprob, hLevy, hMeas, hChar⟩ :=
    ProbabilityTheory.exists_isLevyProcess_pureJump b (ν := nu) hnu
  refine ⟨Ω, m, μ, X, hprob, hLevy, hMeas, ?_⟩
  intro t xi
  have hExp :
      (ProbabilityTheory.LevyKhintchineTriple.mk b 0 nu hnu).exponent xi =
      Kyprianou.Ch01.levyTripleExponent T xi := by
    simp [ProbabilityTheory.LevyKhintchineTriple.exponent_def,
      Kyprianou.Ch01.levyTripleExponent, b, nu, hzero]
    <;> ring
  simpa only [hExp] using hChar t xi
