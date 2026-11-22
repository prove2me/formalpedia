-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiBranchingToCompoundPoissonPathLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:15:33.744275+00:00
-- url     : https://prove2.me/submissions/8bb1d9c7-b436-4404-839d-7ac938bd4a8a

import Theorems.Thm_Kyprianou_Ch01_lampertiBranchingToCompoundPoissonPathLawWithoutMoment
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The moment-restricted forward Lamperti law follows from its stronger
    source-faithful version which does not require a finite offspring mean. -/
theorem solution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hFiniteOffspringMean : Summable
      (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
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
      (P y).map
        (fun ω => fun t : ℝ≥0 => (branchingToPoisson Y t ω : ℤ)) =
      Q.map
        (fun ω => fun t : ℝ≥0 =>
          stoppedIntegerCompoundPoisson y arrival marks t ω) := by
  exact
    Kyprianou.Ch01.lampertiBranchingToCompoundPoissonPathLawWithoutMoment
      Y P law Q rate hRate offspring hNoNullJumps hBranching hMarkov
      hSemigroup hGenerator hInitial hMeas hCadlag arrival marks
      jumpLaw hDriver hSupport hJumpMass
