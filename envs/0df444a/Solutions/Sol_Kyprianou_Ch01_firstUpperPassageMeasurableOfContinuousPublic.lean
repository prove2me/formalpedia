-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassageMeasurableOfContinuousPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:27:01.67129+00:00
-- url     : https://prove2.me/submissions/2bc9c78a-5e0e-4c61-ab03-80eadef5df02

import Theorems.Thm_Kyprianou_Ch01_rationalStrictUpperPassageInfMeasurablePublic
import Theorems.Thm_Kyprianou_Ch01_rationalStrictUpperPassageInfEqualContinuousPublic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) :
    Measurable (firstUpperPassage X s) := by
  have hEq : firstUpperPassage X s =
      (fun ω : Ω =>
        ⨅ r : ℚ,
          if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
            then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
            else ⊤) := by
    funext ω
    exact rationalStrictUpperPassageInfEqualContinuousPublic
      X ω s (hContinuous ω)
  rw [hEq]
  exact rationalStrictUpperPassageInfMeasurablePublic X s hMeas
