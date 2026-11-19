-- Prove2me | solution 1 for Kyprianou.Ch01.finiteMeanCompoundPoissonLinearGrowth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:56:45.594568+00:00
-- url     : https://prove2.me/submissions/962aabd5-7cb7-49cb-ac7e-805e4277ea45

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_finiteMeanRealCompoundPoissonLinearGrowth
import Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonLinearGrowthFromReal
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
      ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ≥0,
          (integerCompoundPoisson y arrival marks t ω : ℝ) ≤
            C * (1 + (t : ℝ)) := by
  intro y
  have hGrowth : ∀ᵐ ω ∂Q,
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ t : ℝ≥0,
          ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤
            K * (1 + (t : ℝ)) :=
    Kyprianou.Ch01.finiteMeanRealCompoundPoissonLinearGrowth
      Q rate hrate offspring hNoZeroJumps hFiniteMean law
      hbranch hMarkov hInitial hRates arrival marks jumpLaw
      hdriver hSupport hJumpMass
  filter_upwards [hGrowth] with ω hω
  obtain ⟨K, hK, hG⟩ := hω
  refine ⟨(y : ℝ) + K + 1, by positivity, ?_⟩
  exact Kyprianou.Ch01.integerCompoundPoissonLinearGrowthFromReal
    y arrival marks ω K hK hG
