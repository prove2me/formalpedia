-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedSmallJumpBandCadlagAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:56:37.49167+00:00
-- url     : https://prove2.me/submissions/573cd940-0ce3-4466-b58d-adfaf5e7d0ad

import Theorems.Thm_Kyprianou_Ch02_prmCompensatedFiniteRegionCadlagAEV1
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun (t : ℝ≥0) => compensatedSmallJumpBand P ν N ε t ω) := by
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
  have hc := Kyprianou.Ch02.prmCompensatedFiniteRegionCadlagAEV1
    P ν N B hB hfinite (∫ x in B, x ∂ν)
  simpa only [compensatedSmallJumpBand, B] using hc
