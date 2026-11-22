-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveMarkovBranching
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:31:28.677222+00:00
-- url     : https://prove2.me/submissions/90c2a14a-d65c-4be9-bd30-88634575bdad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveHasBranchingProperty
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveIsPopulationMarkovSemigroup
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

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
    HasBranchingProperty K ∧ IsPopulationMarkovSemigroup K := by
  constructor
  · exact Kyprianou.Ch01.reverseLampertiNonexplosiveHasBranchingProperty
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion K hRealisation
  · exact Kyprianou.Ch01.reverseLampertiNonexplosiveIsPopulationMarkovSemigroup
      Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hdriver hSupport hJumpMass hNoExplosion K hRealisation
