-- Prove2me | solution 2 for Kyprianou.Ch01.gammaLevyExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:44:57.080211+00:00
-- url     : https://prove2.me/submissions/2d69549f-c4f8-4e6a-86d2-1dcb60d7b8f2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_gammaLevyMeasure_isLevyMeasure
import Theorems.Thm_Kyprianou_Ch01_gammaLevyMeasure_infiniteMass
import Theorems.Thm_Kyprianou_Ch01_gammaExponentIntegralIdentity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Gamma exponent is the exact conjunction of the established analytic
    identities and the remaining infinite-jump-intensity obligation. -/
theorem solution (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta) :
    IsLevyMeasure (gammaLevyMeasure alpha beta) ∧
      gammaLevyMeasure alpha beta Set.univ = ⊤ ∧
      ∀ theta : ℝ,
        IntegrableOn (fun x : ℝ =>
          ((1 : ℂ) - Complex.exp (Complex.I * (theta : ℂ) * (x : ℂ))) *
            ((beta : ℂ) * Complex.exp (-(alpha : ℂ) * (x : ℂ)) / (x : ℂ)))
          (Set.Ioi (0 : ℝ)) ∧
        (∫ x in Set.Ioi (0 : ℝ),
          ((1 : ℂ) - Complex.exp (Complex.I * (theta : ℂ) * (x : ℂ))) *
            ((beta : ℂ) * Complex.exp (-(alpha : ℂ) * (x : ℂ)) / (x : ℂ))
          ∂volume) =
            (beta : ℂ) *
              Complex.log (1 - Complex.I * (theta : ℂ) / (alpha : ℂ)) := by
  refine ⟨Kyprianou.Ch01.gammaLevyMeasure_isLevyMeasure alpha beta ha hb,
    Kyprianou.Ch01.gammaLevyMeasure_infiniteMass alpha beta ha hb, ?_⟩
  intro theta
  exact Kyprianou.Ch01.gammaExponentIntegralIdentity alpha beta ha hb theta
