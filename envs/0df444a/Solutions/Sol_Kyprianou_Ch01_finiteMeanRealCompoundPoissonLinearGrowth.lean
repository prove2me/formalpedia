-- Prove2me | solution 1 for Kyprianou.Ch01.finiteMeanRealCompoundPoissonLinearGrowth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:40:58.987198+00:00
-- url     : https://prove2.me/submissions/7c940068-97fc-423c-9839-5a707a54cec2

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonCompactUpperBoundAE
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonEventualLinearUpperBoundAE
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
    ∀ᵐ ω ∂Q,
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ t : ℝ≥0,
          ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤
            K * (1 + (t : ℝ)) := by
  filter_upwards
    [Kyprianou.Ch01.compoundPoissonEventualLinearUpperBoundAE
      Q rate hrate offspring hFiniteMean
      arrival marks jumpLaw hdriver hSupport hJumpMass,
     Kyprianou.Ch01.compoundPoissonCompactUpperBoundAE
      Q rate hrate arrival marks jumpLaw hdriver]
      with ω hEventual hCompact
  obtain ⟨T, K, hK, hEvent⟩ := hEventual
  obtain ⟨M, hM, hBound⟩ := hCompact T
  have hUpper : 0 ≤ max K M := le_trans hK (le_max_left K M)
  refine ⟨max K M, hUpper, ?_⟩
  intro t
  by_cases ht : t ≤ T
  · calc
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤
          M := hBound t ht
      _ ≤ max K M := le_max_right K M
      _ ≤ max K M * (1 + (t : ℝ)) := by
          nlinarith [mul_nonneg hUpper (NNReal.coe_nonneg t)]
  · have ht' : T ≤ t := le_of_lt (lt_of_not_ge ht)
    calc
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤
          K * (1 + (t : ℝ)) := hEvent t ht'
      _ ≤ max K M * (1 + (t : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (le_max_left K M) (by positivity)
