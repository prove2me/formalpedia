-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveBranchingGenerator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:36:54.018144+00:00
-- url     : https://prove2.me/submissions/2a3e6073-dbed-4709-a435-345d209b06dc

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveDiagonalGenerator
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveOffDiagonalGenerator
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Assemble the original reverse Lamperti Q-matrix from the diagonal and off-diagonal physical-time rates. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    IsBranchingRateGenerator K rate offspring := by
  unfold IsBranchingRateGenerator
  intro y k
  by_cases hk : k = y
  · subst k
    simpa using Kyprianou.Ch01.reverseLampertiNonexplosiveDiagonalGenerator
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion K hRealisation y
  · simpa only [if_neg hk] using
      (Kyprianou.Ch01.reverseLampertiNonexplosiveOffDiagonalGenerator
        Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
        hdriver hSupport hJumpMass hNoExplosion K hRealisation y k hk)
