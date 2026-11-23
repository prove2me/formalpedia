-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiFirstArrivalSurvival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:03:56.677825+00:00
-- url     : https://prove2.me/submissions/ac0386b0-920b-4e0b-91bd-f328a80bfc27

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_exponentialRateSurvival
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
    (y : ℕ) (t : ℝ≥0) :
    (Q {ω | (y : ℝ) * (t : ℝ) <
      ProbabilityTheory.arrival arrival 0 ω}).toReal =
      Real.exp (-((rate : ℝ) * ((y : ℝ) * (t : ℝ)))) := by
  have ht : (0 : ℝ) ≤ (y : ℝ) * (t : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) t.property
  have hr : (0 : ℝ) < (rate : ℝ) := by
    exact_mod_cast hrate
  have hlaw := (hdriver.law_interarrival 0).measureReal_eq
    (p := fun z : ℝ => (y : ℝ) * (t : ℝ) < z)
    (measurableSet_Ioi)
  have hsur := Kyprianou.Ch01.exponentialRateSurvival
    (rate : ℝ) ((y : ℝ) * (t : ℝ)) hr ht
  calc
    (Q {ω | (y : ℝ) * (t : ℝ) <
        ProbabilityTheory.arrival arrival 0 ω}).toReal =
      (ProbabilityTheory.expMeasure (rate : ℝ)).real
        (Set.Ioi ((y : ℝ) * (t : ℝ))) := by
        simpa [Set.Ioi, measureReal_def, ProbabilityTheory.arrival] using hlaw
    _ = _ := hsur

