-- Prove2me | solution 1 for Kyprianou.Ch02.pureJumpMarginalExplicitLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:20:21.862201+00:00
-- url     : https://prove2.me/submissions/2a6cd5f6-4072-4f46-b22b-cc78a4766b3e

import Theorems.Thm_Kyprianou_Ch01_levyProcess_exists_zeroGaussianTargeted
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) :
    ∃ (R : Measure ℝ), IsProbabilityMeasure R ∧
      ∀ ξ : ℝ, charFun R ξ = Complex.exp
        (Complex.I * ((T.drift * ξ : ℝ) : ℂ) +
          ∫ y, ProbabilityTheory.levyCompensatedIntegrand ξ y ∂T.levyMeasure) := by
  let U : ProbabilityTheory.LevyKhintchineTriple :=
    ⟨T.drift, 0, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩
  obtain ⟨Ω, m, P, X, hP, hX, hm, hc⟩ :=
    Kyprianou.Ch01.levyProcess_exists_zeroGaussianTargeted U rfl
  letI : MeasurableSpace Ω := m
  letI : IsProbabilityMeasure P := hP
  refine ⟨P.map (X 1), Measure.isProbabilityMeasure_map (hm 1).aemeasurable, ?_⟩
  intro ξ
  simpa [U, Kyprianou.Ch01.levyTripleExponent] using hc 1 ξ
