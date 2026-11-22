-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiForwardPathMapsAEMeasurableWithoutMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:35:10.284153+00:00
-- url     : https://prove2.me/submissions/4b18c442-b78c-4bdd-9599-fa79517c5481

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_branchingToPoissonPathAEMeasurableFromCadlag
import Theorems.Thm_Kyprianou_Ch01_stoppedIntegerCompoundPoissonPathAEMeasurableFromDriver

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The corrected Lamperti path-map measurability theorem splits into
the branching inverse-clock component and the marked Poisson component. -/
theorem solution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω))
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ y : ℕ,
      AEMeasurable
        (fun ω : Ω => fun t : ℝ≥0 =>
          (branchingToPoisson Y t ω : ℤ)) (P y) ∧
      AEMeasurable
        (fun ω : Ω' => fun t : ℝ≥0 =>
          stoppedIntegerCompoundPoisson y arrival marks t ω) Q := by
  intro y
  constructor
  · exact Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromCadlag
      Y (P y) hMeas (hCadlag y)
  · exact Kyprianou.Ch01.stoppedIntegerCompoundPoissonPathAEMeasurableFromDriver
      Q rate hRate offspring hNoNullJumps
      arrival marks jumpLaw hDriver hSupport hJumpMass y
