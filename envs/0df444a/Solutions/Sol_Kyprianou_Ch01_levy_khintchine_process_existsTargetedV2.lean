-- Prove2me | solution 1 for Kyprianou.Ch01.levy_khintchine_process_existsTargetedV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T20:18:01.975521+00:00
-- url     : https://prove2.me/submissions/4b1edfc3-cfe5-41b6-82af-c01291ebd614

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Theorems.Thm_Kyprianou_Ch01_levyProcess_exists_zeroGaussianTargeted
import Theorems.Thm_Kyprianou_Ch01_levyProcess_exists_positiveGaussianTargeted
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
    (T : ProbabilityTheory.LevyKhintchineTriple) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧
        (∀ t, Measurable (X t)) ∧
        ∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (μ.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) * Kyprianou.Ch01.levyTripleExponent T ξ) := by
  by_cases hzero : T.gaussianVariance = 0
  · exact Kyprianou.Ch01.levyProcess_exists_zeroGaussianTargeted T hzero
  · have hpos : 0 < T.gaussianVariance :=
      lt_of_le_of_ne (show (0 : ℝ≥0) ≤ T.gaussianVariance from bot_le) (Ne.symm hzero)
    exact Kyprianou.Ch01.levyProcess_exists_positiveGaussianTargeted T hpos
