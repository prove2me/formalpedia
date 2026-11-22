-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveConstructsBranchingLaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:41:24.668837+00:00
-- url     : https://prove2.me/submissions/264cf8df-2fa3-49a0-97d1-7fbafbc726eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosivePopulationLawExists
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveMarkovBranching
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveBranchingGenerator
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The reverse Lamperti probability law, Markov-branching structure and
generator combine to construct a conservative branching semigroup. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation
            (integerCompoundPoisson y arrival marks) s ω) :
    ∃ K : PopulationLaws,
      HasBranchingProperty K ∧
      IsPopulationMarkovSemigroup K ∧
      (∀ y : ℕ, K y 0 = PMF.pure y) ∧
      IsBranchingRateGenerator K rate offspring ∧
      ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
        K y t k =
          Q {ω | (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat = k} := by
  obtain ⟨K, hKinit, hKlaw⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosivePopulationLawExists
      Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion
  obtain ⟨hKbranch, hKmarkov⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveMarkovBranching
      Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion
      K hKlaw
  have hKgen : IsBranchingRateGenerator K rate offspring :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveBranchingGenerator
      Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion
      K hKlaw
  exact ⟨K, hKbranch, hKmarkov, hKinit, hKgen, hKlaw⟩
