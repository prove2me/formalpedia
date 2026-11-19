-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiCompoundPoissonToBranchingLaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:33:48.451809+00:00
-- url     : https://prove2.me/submissions/f69474c5-4ac7-438b-90d0-fc111d429709
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_lampertiCompoundPoissonToBranchingLawNonexplosive
import Theorems.Thm_Kyprianou_Ch01_finiteMeanCompoundPoissonClockNonexplosion
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
    ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      law y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k} := by
  have hClock : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation
            (integerCompoundPoisson y arrival marks) s ω :=
    Kyprianou.Ch01.finiteMeanCompoundPoissonClockNonexplosion
      Q rate hrate offspring hNoZeroJumps hFiniteMean law
      hbranch hMarkov hInitial hRates arrival marks jumpLaw
      hdriver hSupport hJumpMass
  exact Kyprianou.Ch01.lampertiCompoundPoissonToBranchingLawNonexplosive
    Q rate hrate offspring hNoZeroJumps law hbranch
    hMarkov hInitial hRates arrival marks jumpLaw
    hdriver hSupport hJumpMass hClock
