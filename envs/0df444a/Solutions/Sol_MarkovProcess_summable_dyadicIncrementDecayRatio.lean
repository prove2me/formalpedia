-- Prove2me | solution 1 for MarkovProcess.summable_dyadicIncrementDecayRatio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:34:27.536487+00:00
-- url     : https://prove2.me/submissions/b31afb6f-1c3a-4a51-a9dc-95bc39904bd1

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_FiniteGridFoundations
import Definitions.Def_MarkovProcess_DyadicIncrementScalars
import Theorems.Thm_MarkovProcess_dyadicIncrementDecayRatio_lt_one
open MarkovProcess MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution {p q γ : ℝ} (M : ℝ≥0) (hp : 0 < p)
    (hγ : γ < (q - 1) / p) :
    Summable (fun n : ℕ ↦ M * dyadicIncrementDecayRatio p q γ ^ n) :=
  (NNReal.summable_geometric (dyadicIncrementDecayRatio_lt_one hp hγ)).mul_left M
