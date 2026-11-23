-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonFirstArrivalCDFLinearBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:44:06.225274+00:00
-- url     : https://prove2.me/submissions/11d1f002-d04d-4275-955a-222ec57fcff3

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (u : ℝ) (hu : 0 ≤ u) :
    (Q {ω | ProbabilityTheory.arrival arrival 0 ω ≤ u}).toReal ≤
      (rate : ℝ) * u := by
  have hr : (0 : ℝ) < (rate : ℝ) := by
    exact_mod_cast hrate
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (rate : ℝ)) :=
    isProbabilityMeasure_expMeasure hr
  have hlaw := (hdriver.law_interarrival 0).measureReal_eq
    (p := fun z : ℝ => z ≤ u) measurableSet_Iic
  have heq :
      (Q {ω | ProbabilityTheory.arrival arrival 0 ω ≤ u}).toReal =
        (ProbabilityTheory.expMeasure (rate : ℝ)).real (Set.Iic u) := by
    simpa [Set.Iic, measureReal_def, ProbabilityTheory.arrival] using hlaw
  calc
    (Q {ω | ProbabilityTheory.arrival arrival 0 ω ≤ u}).toReal =
        (ProbabilityTheory.expMeasure (rate : ℝ)).real (Set.Iic u) := heq
    _ = 1 - Real.exp (-((rate : ℝ) * u)) := by
      rw [← cdf_eq_real, cdf_expMeasure_eq hr, if_pos hu]
    _ ≤ (rate : ℝ) * u := by
      nlinarith [Real.add_one_le_exp (-((rate : ℝ) * u))]

