-- Prove2me | solution 1 for Kyprianou.Ch01.finiteMeanCompoundPoissonClockNonexplosion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:36:51.580361+00:00
-- url     : https://prove2.me/submissions/74d5120c-b5d9-4bf5-a4d4-132713397a35

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_finiteMeanCompoundPoissonLinearGrowth
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationDivergesOfLinearUpperBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (hFiniteMean : Summable
      (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation
            (integerCompoundPoisson y arrival marks) s ω := by
  intro y
  have hLinear : ∀ᵐ ω ∂Q,
      ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ≥0,
          (integerCompoundPoisson y arrival marks t ω : ℝ) ≤
            C * (1 + (t : ℝ)) :=
    Kyprianou.Ch01.finiteMeanCompoundPoissonLinearGrowth
      Q rate hrate offspring hNoZeroJumps hFiniteMean
      law hbranch hMarkov hInitial hRates arrival marks
      jumpLaw hdriver hSupport hJumpMass y
  filter_upwards [hLinear] with ω hw
  obtain ⟨C, hC, hUpper⟩ := hw
  exact Kyprianou.Ch01.reciprocalOccupationDivergesOfLinearUpperBound
    (integerCompoundPoisson y arrival marks) ω C hC hUpper
