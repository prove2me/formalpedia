-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiTwoEventReturnUpperBound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:43:11.358377+00:00
-- url     : https://prove2.me/submissions/1454172c-7c83-4a87-ac98-e31925400ba7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoEventReturnProbabilitySandwich
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonMarkedFirstTwoClockUpperBound
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
    ∀ y : ℕ, 0 < y → ∀ t : ℝ, 0 ≤ t →
      (0 ≤ ((K y (Real.toNNReal t)) y).toReal -
          (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
            ProbabilityTheory.arrival arrival 0 ω}).toReal) ∧
      (((K y (Real.toNNReal t)) y).toReal -
          (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
            ProbabilityTheory.arrival arrival 0 ω}).toReal) ≤
        ((rate : ℝ) * (y : ℝ)) * t * (∑' k : ℕ, (offspring k).toReal *
          (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * t)))) := by
  intro y hy t ht
  have hSand :=
    Kyprianou.Ch01.reverseLampertiTwoEventReturnProbabilitySandwich
      Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hdriver hSupport hJumpMass hNoExplosion
      K hRealisation hBefore y hy t ht
  have hMark :=
    Kyprianou.Ch01.compoundPoissonMarkedFirstTwoClockUpperBound
      Q rate hrate offspring arrival marks jumpLaw
      hdriver hJumpMass y (Real.toNNReal t)
  rw [Real.coe_toNNReal t ht] at hSand hMark
  rw [hRealisation y (Real.toNNReal t) y]
  rw [Real.coe_toNNReal t ht]
  constructor
  · exact sub_nonneg.mpr hSand.1
  · linarith [hSand.2, hMark]

