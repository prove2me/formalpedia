-- Prove2me | solution 2 for Kyprianou.Ch01.reverseLampertiNonexplosivePositiveDiagonalGenerator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:24:06.007815+00:00
-- url     : https://prove2.me/submissions/6970077b-85dc-4b2b-8c3d-4bff47e8afee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiReturnAfterFirstArrivalZeroSlope
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalSurvival
import Theorems.Thm_Kyprianou_Ch01_expNegNNRealHasDerivWithinAtZero
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
        (fun t : ℝ => ((K y (Real.toNNReal t)) y).toReal)
        (-((rate : ℝ) * (y : ℝ)))
        (Set.Ici 0) 0 := by
  intro y hy
  have hRem :=
    Kyprianou.Ch01.reverseLampertiReturnAfterFirstArrivalZeroSlope
      Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hdriver hSupport hJumpMass hNoExplosion
      K hRealisation y hy
  have hFirst (t : ℝ) :
      (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
        ProbabilityTheory.arrival arrival 0 ω}).toReal =
        Real.exp (-(((rate : ℝ) * (y : ℝ)) *
          (Real.toNNReal t : ℝ))) := by
    convert Kyprianou.Ch01.reverseLampertiFirstArrivalSurvival
      Q rate hrate arrival marks jumpLaw hdriver
      y (Real.toNNReal t) using 1 <;> ring
  have hExp :=
    Kyprianou.Ch01.expNegNNRealHasDerivWithinAtZero
      ((rate : ℝ) * (y : ℝ))
  have hSum := hRem.add hExp
  have hFun : (fun t : ℝ =>
        ((K y (Real.toNNReal t)) y).toReal -
        (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
           ProbabilityTheory.arrival arrival 0 ω}).toReal +
        Real.exp (-(((rate : ℝ) * (y : ℝ)) *
           (Real.toNNReal t : ℝ)))) =
      (fun t : ℝ => ((K y (Real.toNNReal t)) y).toReal) := by
    funext t
    rw [hFirst]
    ring
  have hSum' : HasDerivWithinAt
      (fun t : ℝ =>
        ((K y (Real.toNNReal t)) y).toReal -
        (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
          ProbabilityTheory.arrival arrival 0 ω}).toReal +
        Real.exp (-(((rate : ℝ) * (y : ℝ)) *
          (Real.toNNReal t : ℝ))))
      (0 + -((rate : ℝ) * (y : ℝ))) (Set.Ici 0) 0 := hSum
  rw [hFun] at hSum'
  simpa only [zero_add, neg_mul] using hSum'
