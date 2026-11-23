-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiReturnAfterFirstArrivalZeroSlopeGivenNoJumpPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:16:10.802198+00:00
-- url     : https://prove2.me/submissions/1a14dfd6-9b28-4b07-a42f-9d712a023c38

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_pmfMarkedSecondEventFactorTendsZero
import Theorems.Thm_Kyprianou_Ch01_zeroRightDerivativeOfLinearSmallFactor
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoEventReturnUpperBound
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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (hBefore : ∀ (z : ℕ) (u : ℝ≥0) (ω : Ω),
      (u : ℝ) < ProbabilityTheory.arrival arrival 0 ω →
        integerCompoundPoisson z arrival marks u ω = (z : ℤ)) :
    ∀ y : ℕ, 0 < y →
      HasDerivWithinAt
        (fun t : ℝ =>
          ((K y (Real.toNNReal t)) y).toReal -
          (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
              ProbabilityTheory.arrival arrival 0 ω}).toReal)
        0 (Set.Ici 0) 0  := by
  intro y hy
  let D : ℝ → ℝ := fun t =>
    ((K y (Real.toNNReal t)) y).toReal -
    (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
      ProbabilityTheory.arrival arrival 0 ω}).toReal
  let H : ℝ → ℝ := fun t => (∑' k : ℕ, (offspring k).toReal *
    (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * t))))
  have hSmall : Tendsto H
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [H] using
      (Kyprianou.Ch01.pmfMarkedSecondEventFactorTendsZero
        offspring rate y)
  have hBound (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ D t ∧ D t ≤
        ((rate : ℝ) * (y : ℝ)) * t * H t := by
    simpa [D, H] using
      (Kyprianou.Ch01.reverseLampertiTwoEventReturnUpperBound
        Q rate hrate offspring hNoZeroJumps arrival marks
        jumpLaw hdriver hSupport hJumpMass hNoExplosion
        K hRealisation hBefore y hy t ht)
  exact Kyprianou.Ch01.zeroRightDerivativeOfLinearSmallFactor
    D H ((rate : ℝ) * (y : ℝ)) hSmall hBound
