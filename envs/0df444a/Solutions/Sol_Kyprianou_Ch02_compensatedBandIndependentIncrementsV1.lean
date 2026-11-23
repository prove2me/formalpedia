-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedBandIndependentIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:57:04.350426+00:00
-- url     : https://prove2.me/submissions/d8ce4924-4c48-44d5-b24c-46c69d3ca715

import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionIndependentIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_independentIncrementsSubLinearDriftV1
import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ProbabilityTheory.HasIndependentIncrements
      (Kyprianou.compensatedSmallJumpBand P ν N ε) P := by
  let B : Set ℝ := {x | ε ≤ |x| ∧ |x| < 1}
  have hB : MeasurableSet B := by
    exact (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hfinite : ν B < ⊤ := by
    have hle : ν B ≤ ν {x : ℝ | ε ≤ |x|} := by
      apply measure_mono
      intro x hx
      exact hx.1
    exact lt_of_le_of_lt hle
      (ProbabilityTheory.IsLevyMeasure.measure_setOf_abs_ge_lt_top hν hε)
  have hraw : ProbabilityTheory.HasIndependentIncrements
      (fun (t : ℝ≥0) (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) P :=
    Kyprianou.Ch02.prmFiniteRegionIndependentIncrementsV1 P ν N B hB hfinite
  have h := Kyprianou.Ch02.independentIncrementsSubLinearDriftV1
    P (fun (t : ℝ≥0) (ω : Ω) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))
    (∫ x in B, x ∂ν) hraw
  change ProbabilityTheory.HasIndependentIncrements
    (fun (t : ℝ≥0) (ω : Ω) =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
        (t : ℝ) * ∫ x in B, x ∂ν) P
  exact h
