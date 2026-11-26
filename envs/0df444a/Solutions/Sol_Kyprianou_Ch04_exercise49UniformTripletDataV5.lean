-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49UniformTripletDataV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:12:17.473456+00:00
-- url     : https://prove2.me/submissions/8f4ae3cb-4fde-47dc-8285-2e91d0f321ab

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49TripletBridgeV5
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (b : ℝ) :
    ∃ T : ProbabilityTheory.LevyKhintchineTriple,
      (T.gaussianVariance = 0 ∧
        (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂T.levyMeasure) < ⊤) ∧
      b = T.drift - ∫ y in Ioo (-1 : ℝ) 1, y ∂T.levyMeasure ∧
      ∀ ξ : ℝ, Kyprianou.Ch01.levyTripleExponent T ξ =
        Complex.I * b * ξ + (charFun ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ξ - 1) := by
  let ν : Measure ℝ := volume.restrict (Ioo (-1 : ℝ) 0)
  letI : IsProbabilityMeasure ν := ⟨by simp [ν,Measure.restrict_apply_univ,Real.volume_Ioo]⟩
  have hz : ν {0} = 0 := by simp [ν,Measure.restrict_apply,measurableSet_singleton]
  have hν : ProbabilityTheory.IsLevyMeasure ν := ProbabilityTheory.IsLevyMeasure.of_isFiniteMeasure hz
  have hL : LevyFoundations.isLevyMeasure ((1 : ENNReal) • ν) := by
    simpa only [one_smul,LevyFoundations.isLevyMeasure,ProbabilityTheory.IsLevyMeasure] using hν
  let T : ProbabilityTheory.LevyKhintchineTriple :=
    ⟨b + ∫ y in Ioo (-1 : ℝ) 1, y ∂ν,0,ν,hν⟩
  refine ⟨T,⟨rfl,?_⟩,?_,?_⟩
  · change (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂ν) < ⊤
    calc
      _ ≤ ∫⁻ _ in Ioo (-1 : ℝ) 1, (1 : ENNReal) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (μ := ν) (measurableSet_Ioo : MeasurableSet (Ioo (-1 : ℝ) 1))] with y hy
        exact ENNReal.ofReal_le_one.mpr (abs_lt.mpr hy).le
      _ = ν (Ioo (-1 : ℝ) 1) := by simp
      _ < ⊤ := measure_lt_top _ _
  · change b = b + (∫ y in Ioo (-1 : ℝ) 1, y ∂ν) - _
    ring
  · exact exercise49TripletBridgeV5 b ν hν hL
