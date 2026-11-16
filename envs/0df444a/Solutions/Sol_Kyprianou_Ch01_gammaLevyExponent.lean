-- Prove2me | solution 1 for Kyprianou.Ch01.gammaLevyExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:15:25.3755+00:00
-- url     : https://prove2.me/submissions/061b8fc9-5665-4906-b0c6-f222357f0bae

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

theorem solution
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta) :
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
            (beta : ℂ) * Complex.log
              (1 - Complex.I * (theta : ℂ) / (alpha : ℂ)) := by
  exact ⟨gammaLevyMeasure_isLevyMeasure alpha beta ha hb,
    gammaLevyMeasure_infiniteMass alpha beta ha hb,
    fun theta => gammaExponentIntegralIdentity alpha beta ha hb theta⟩
