-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiReturnAfterFirstArrivalZeroSlope
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:02:16.115118+00:00
-- url     : https://prove2.me/submissions/2e10f573-dd74-4a18-9619-fb89c7da93b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseIntegerCompoundPoissonConstantBeforeFirstArrival
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiReturnAfterFirstArrivalZeroSlopeGivenNoJumpPath
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
    ∀ y : ℕ, 0 < y →
      HasDerivWithinAt
        (fun t : ℝ =>
          ((K y (Real.toNNReal t)) y).toReal -
          (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
              ProbabilityTheory.arrival arrival 0 ω}).toReal)
        0 (Set.Ici 0) 0 := by
  have hBefore (z : ℕ) (u : ℝ≥0) (ω : Ω)
      (hu : (u : ℝ) < ProbabilityTheory.arrival arrival 0 ω) :
      integerCompoundPoisson z arrival marks u ω = (z : ℤ) :=
    Kyprianou.Ch01.reverseIntegerCompoundPoissonConstantBeforeFirstArrival
      z arrival marks u ω hu
  exact Kyprianou.Ch01.reverseLampertiReturnAfterFirstArrivalZeroSlopeGivenNoJumpPath
    Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
    hdriver hSupport hJumpMass hNoExplosion K hRealisation hBefore

