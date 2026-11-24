-- Prove2me | solution 1 for Kyprianou.Ch02.levyWholePathLawEqOfCharFunV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:53:42.382971+00:00
-- url     : https://prove2.me/submissions/e54fc262-1c1c-4476-aa82-aec4e4249009

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyWholePathLawEqOfMarginalLawsV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false


/-- Source-faithful Chapter 2 proof. -/
theorem solution
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hchar : ∀ t : ℝ≥0, ∀ ξ : ℝ,
      charFun (P.map (X t)) ξ = charFun (Q.map (Y t)) ξ) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X t ω) P =
      Measure.map (fun ω : Λ => fun t : ℝ≥0 => Y t ω) Q := by
  apply Kyprianou.Ch02.levyWholePathLawEqOfMarginalLawsV1 P Q X Y hX hY
  intro t
  haveI : IsProbabilityMeasure (P.map (X t)) :=
    Measure.isProbabilityMeasure_map
      (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t)
  haveI : IsProbabilityMeasure (Q.map (Y t)) :=
    Measure.isProbabilityMeasure_map
      (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 Q Y hY t)
  apply Measure.ext_of_charFun
  exact funext (hchar t)
