-- Prove2me | solution 1 for Kyprianou.Ch01.characteristicExponentialMartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:12:27.180397+00:00
-- url     : https://prove2.me/submissions/726c39f1-eacc-4f7a-b5cc-7400fb912848

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_characteristicExponential_integrable
import Theorems.Thm_Kyprianou_Ch01_characteristicExponentialConditionalExpectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (Psi : ℂ)
    (hchar : ∀ t : ℝ≥0,
      charFun (P.map (X t)) theta =
        Complex.exp (-((t : ℝ) : ℂ) * Psi)) :
    let M : ℝ≥0 → Ω → ℂ :=
      fun t ω =>
        Complex.exp (Complex.I * (theta : ℂ) * (X t ω : ℂ) +
          ((t : ℝ) : ℂ) * Psi)
    ∀ (s t : ℝ≥0), s ≤ t →
      Integrable (M t) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
          (∫ ω in A, M t ω ∂P) =
            (∫ ω in A, M s ω ∂P) := by
  dsimp
  intro s t hst
  constructor
  · exact Kyprianou.Ch01.characteristicExponential_integrable
      P X hmeas theta Psi t
  · exact Kyprianou.Ch01.characteristicExponentialConditionalExpectation
      P X hX hmeas theta Psi hchar s t hst
