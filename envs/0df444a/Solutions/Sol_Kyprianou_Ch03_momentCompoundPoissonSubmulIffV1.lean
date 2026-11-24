-- Prove2me | solution 1 for Kyprianou.Ch03.momentCompoundPoissonSubmulIffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:54:14.741248+00:00
-- url     : https://prove2.me/submissions/ef010665-4c4c-41c9-ba74-683564bf1d3a

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_momentCPSeriesIffFiniteV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g) :
    Integrable g (KSATSingleFlip.Connect.compoundPoisson mu) ↔ Integrable g mu := by
  have key (m : Measure ℝ) : Integrable g m ↔
      (∫⁻ x, ENNReal.ofReal (g x) ∂m) < ⊤ := by
    exact ⟨fun h => (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hg.1)).mp h.2,
      fun h => ⟨hg_meas.aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hg.1)).mpr h⟩⟩
  rw [key, key]
  exact Kyprianou.Ch03.momentCPSeriesIffFiniteV1 mu g hg hg_meas
